;; Proof reconstruction from E-graph paths.
;; Following Lean 4's grind Proof.lean.
;;
;; Builds kernel-verified CIC proof terms (Eq.refl, Eq.symm, Eq.trans,
;; congrArg, congrFun, congr) by walking the transitivity chains stored
;; in E-graph ENodes.

(ns ansatz.tactic.grind.proof
  "Build CIC proof terms from E-graph equivalence paths."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.grind.egraph :as eg]))

;; ============================================================
;; Cached names
;; ============================================================

(def ^:private eq-refl-name (name/from-string "Eq.refl"))
(def ^:private eq-symm-name (name/from-string "Eq.symm"))
(def ^:private eq-trans-name (name/from-string "Eq.trans"))
(def ^:private congr-arg-name (name/from-string "congrArg"))
(def ^:private congr-fun-name (name/from-string "congrFun"))
(def ^:private congr-name (name/from-string "congr"))
(def ^:private eq-name (name/from-string "Eq"))

;; ============================================================
;; Proof term builders — CIC primitives
;; ============================================================

(defn- infer-type [st expr]
  (tc/infer-type st expr))

(defn- get-sort-level
  "Get the universe level of a type."
  [st ty]
  (let [sort (try (let [s (tc/infer-type st ty)]
                    (#'tc/cached-whnf st s))
                  (catch Exception _ nil))]
    (if (and sort (e/sort? sort))
      (e/sort-level sort)
      lvl/zero)))

(defn mk-eq-refl
  "Build @Eq.refl.{u} α a : @Eq.{u} α a a"
  [st a]
  (let [alpha (infer-type st a)
        u (get-sort-level st alpha)]
    (e/app* (e/const' eq-refl-name [u]) alpha a)))

(defn mk-eq-symm
  "Build @Eq.symm.{u} α a b h : @Eq α b a  (from h : @Eq α a b)"
  [st alpha a b h]
  (let [u (get-sort-level st alpha)]
    (e/app* (e/const' eq-symm-name [u]) alpha a b h)))

(defn mk-eq-trans
  "Build @Eq.trans.{u} α a b c h1 h2 : @Eq α a c
   (from h1 : @Eq α a b, h2 : @Eq α b c)"
  [st alpha a b c h1 h2]
  (let [u (get-sort-level st alpha)]
    (e/app* (e/const' eq-trans-name [u]) alpha a b c h1 h2)))

(defn mk-congr-arg
  "Build @congrArg.{u,v} α β a b f h : @Eq β (f a) (f b)
   (from h : @Eq α a b)"
  [st alpha beta a b f h]
  (let [u (get-sort-level st alpha)
        v (get-sort-level st beta)]
    (e/app* (e/const' congr-arg-name [u v])
            alpha beta a b f h)))

(defn mk-congr-fun
  "Build @congrFun.{u,v} α β f g h a : @Eq (β a) (f a) (g a)
   (from h : @Eq (α → β) f g)"
  [st alpha beta f g h a]
  (let [u (get-sort-level st alpha)
        v (get-sort-level st beta)]
    (e/app* (e/const' congr-fun-name [u v])
            alpha beta f g h a)))

(defn mk-congr
  "Build @congr.{u,v} α β f g a b h1 h2 : @Eq β (f a) (g b)
   (from h1 : @Eq (α→β) f g, h2 : @Eq α a b)"
  [st alpha beta f g a b h1 h2]
  (let [u (get-sort-level st alpha)
        v (get-sort-level st beta)]
    (e/app* (e/const' congr-name [u v])
            alpha beta f g a b h1 h2)))

;; ============================================================
;; Extract Eq components from type
;; ============================================================

(defn- extract-eq
  "If expr is @Eq α a b, return [α a b]. Otherwise nil."
  [st expr]
  (let [w (#'tc/cached-whnf st expr)
        [h args] (e/get-app-fn-args w)]
    (when (and (e/const? h) (= (e/const-name h) eq-name) (= 3 (count args)))
      [(nth args 0) (nth args 1) (nth args 2)])))

;; ============================================================
;; Find common ancestor in transitivity chains
;; Following Lean 4 Proof.lean:72
;; ============================================================

(defn- find-common
  "Find the common ancestor of lhs and rhs in the E-graph's transitivity chains.
   Walk from lhs to root marking visited nodes, then walk from rhs to find first marked."
  [gs lhs rhs]
  ;; Walk from lhs to root, collecting visited node indices
  (let [visited (loop [curr lhs seen #{}]
                  (let [node (eg/get-enode gs curr)
                        seen (conj seen (:idx node))]
                    (if-let [target (:target node)]
                      (recur target seen)
                      seen)))]
    ;; Walk from rhs to root, find first node in visited set
    (loop [curr rhs]
      (let [node (eg/get-enode gs curr)]
        (if (contains? visited (:idx node))
          curr
          (if-let [target (:target node)]
            (recur target)
            ;; Both should reach the same root — if we get here,
            ;; the common ancestor is the root itself
            curr))))))

;; ============================================================
;; Realize a single proof step
;; Following Lean 4 Proof.lean:273
;; ============================================================

(declare mk-eq-proof mk-congr-proof)

(declare mk-congr-proof)

(defn- realize-proof-step
  "Realize a single proof step from the E-graph.
   Given proof of (a = target) or (target = a) depending on flipped,
   return the actual CIC proof term."
  [gs st a target proof flipped]
  (cond
    ;; Congruence placeholder — build congruence proof
    (= proof :congr-placeholder)
    (mk-congr-proof gs st a target)

    ;; Regular proof — flip if needed
    flipped
    (let [alpha (infer-type st a)]
      (mk-eq-symm st alpha target a proof))

    :else proof))

;; ============================================================
;; Build proof by walking transitivity chain
;; Following Lean 4 Proof.lean:282 (mkProofTo) and :295 (mkProofFrom)
;; ============================================================

(defn- mk-proof-to
  "Walk from `start` toward `common`, accumulating a proof of start = common.
   Returns a CIC proof term, or nil if start IS common."
  [gs st start common]
  (if (.equals start common)
    nil  ;; no proof needed
    (loop [curr start acc nil]
      (if (.equals curr common)
        acc
        (let [node (eg/get-enode gs curr)
              target (:target node)
              _ (when-not target
                  (throw (ex-info "E-graph proof: broken chain, no target"
                                  {:curr curr :common common})))
              step-proof (realize-proof-step gs st curr target
                                             (:proof node) (:flipped node))]
          ;; step-proof : curr = target
          ;; acc : start = curr (or nil if first step)
          (let [new-acc (if acc
                          (let [alpha (infer-type st start)]
                            (mk-eq-trans st alpha start curr target acc step-proof))
                          step-proof)]
            (recur target new-acc)))))))

(defn- mk-proof-from
  "Walk from `end` toward `common`, building a proof of common = end.
   We walk forward from common's perspective but traverse backward."
  [gs st end common]
  (if (.equals end common)
    nil
    ;; Build the proof backward: walk from end to common, collect steps,
    ;; then reverse and compose
    (let [steps (loop [curr end steps []]
                  (if (.equals curr common)
                    steps
                    (let [node (eg/get-enode gs curr)
                          target (:target node)
                          _ (when-not target
                              (throw (ex-info "E-graph proof: broken chain"
                                              {:curr curr :common common})))]
                      (recur target (conj steps {:from curr :target target
                                                 :proof (:proof node)
                                                 :flipped (:flipped node)})))))]
      ;; steps is [end→..., ...→common]. We need common→...→end.
      ;; Each step {from=A, target=B, proof=P, flipped=F} means A→B.
      ;; Reversed: B→A with flipped proof.
      (reduce (fn [acc {:keys [from target proof flipped]}]
                ;; Original: from = target (or target = from if flipped)
                ;; We want: target = from (reversed direction)
                (let [step-proof (realize-proof-step gs st target from proof (not flipped))]
                  (if acc
                    (let [alpha (infer-type st common)]
                      (mk-eq-trans st alpha common target from acc step-proof))
                    step-proof)))
              nil
              (reverse steps)))))

;; ============================================================
;; Congruence proof construction
;; Following Lean 4 Proof.lean:166 (mkCongrDefaultProof)
;; ============================================================

(defn- mk-congr-proof
  "Build a congruence proof for two applications f(a₁..aₙ) = g(b₁..bₙ)
   where aᵢ ~ bᵢ in the E-graph."
  [gs st lhs rhs]
  (let [[lhs-head lhs-args] (e/get-app-fn-args lhs)
        [rhs-head rhs-args] (e/get-app-fn-args rhs)]
    (cond
      ;; Both are applications with same arity
      (and (= (count lhs-args) (count rhs-args)) (pos? (count lhs-args)))
      (let [n (count lhs-args)
            ;; If heads differ, start with a proof of head equality
            initial-fn-proof (when (and (not (.equals lhs-head rhs-head))
                                        (eg/is-eqv gs lhs-head rhs-head))
                               (mk-eq-proof gs st lhs-head rhs-head))]
        ;; Build bottom-up: start from innermost applications
        ;; For f(a) = f(b): congrArg f (proof a=b)
        ;; For f(a₁,a₂) = g(b₁,b₂): congr (proof f=g) (proof a₁=b₁) ...
        (loop [i 0 fn-proof initial-fn-proof lhs-fn lhs-head rhs-fn rhs-head]
          (if (>= i n)
            (or fn-proof (mk-eq-refl st lhs))  ;; all args identical → refl
            (let [a (nth lhs-args i)
                  b (nth rhs-args i)
                  ;; Check if we need to continue peeling
                  remaining-lhs (reduce e/app lhs-fn (take (inc i) lhs-args))
                  remaining-rhs (reduce e/app rhs-fn (take (inc i) rhs-args))]
              (if (= i (dec n))
                ;; Last argument — build the final proof
                (if (.equals a b)
                  (if fn-proof
                    ;; f ≠ g but last arg same: congrFun fn-proof a
                    (let [alpha (infer-type st a)
                          beta-expr (infer-type st (e/app lhs-fn a))]
                      (mk-congr-fun st alpha beta-expr lhs-fn rhs-fn fn-proof a))
                    ;; Everything identical → refl
                    (mk-eq-refl st lhs))
                  ;; Last arg differs
                  (let [arg-proof (mk-eq-proof gs st a b)
                        alpha (infer-type st a)
                        beta (infer-type st (e/app lhs-fn a))]
                    (if fn-proof
                      ;; Both function and arg differ: congr
                      (mk-congr st alpha beta lhs-fn rhs-fn a b fn-proof arg-proof)
                      ;; Only arg differs: congrArg
                      (mk-congr-arg st alpha beta a b lhs-fn arg-proof))))
                ;; Not last argument — accumulate function proof
                (if (.equals a b)
                  (recur (inc i) fn-proof
                         (e/app lhs-fn a) (e/app rhs-fn b))
                  ;; Arg differs — build partial proof and continue
                  (let [arg-proof (mk-eq-proof gs st a b)
                        alpha (infer-type st a)
                        beta (infer-type st (e/app lhs-fn a))
                        new-fn-proof (if fn-proof
                                       (mk-congr st alpha beta lhs-fn rhs-fn a b fn-proof arg-proof)
                                       (mk-congr-arg st alpha beta a b lhs-fn arg-proof))]
                    (recur (inc i) new-fn-proof
                           (e/app lhs-fn a) (e/app rhs-fn b)))))))))

      ;; Fallback: try refl (terms might be def-eq)
      :else
      (mk-eq-refl st lhs))))

;; ============================================================
;; Main entry point — mk-eq-proof
;; Following Lean 4 Proof.lean:311
;; ============================================================

(defn mk-eq-proof
  "Build a kernel-verifiable CIC proof term for lhs = rhs from E-graph paths.
   Requires that lhs and rhs are in the same equivalence class."
  [gs st lhs rhs]
  ;; Fast path: equal terms → Eq.refl
  (if (.equals lhs rhs)
    (mk-eq-refl st lhs)
    ;; Find common ancestor in transitivity chains
    (let [common (find-common gs lhs rhs)
          ;; Build proof: lhs = common
          lhs-to-common (mk-proof-to gs st lhs common)
          ;; Build proof: common = rhs
          common-to-rhs (mk-proof-from gs st rhs common)]
      (cond
        ;; Only left path needed
        (and lhs-to-common (nil? common-to-rhs))
        lhs-to-common

        ;; Only right path needed
        (and (nil? lhs-to-common) common-to-rhs)
        common-to-rhs

        ;; Both paths: compose with Eq.trans
        (and lhs-to-common common-to-rhs)
        (let [alpha (infer-type st lhs)]
          (mk-eq-trans st alpha lhs common rhs lhs-to-common common-to-rhs))

        ;; Neither path: both are common (shouldn't happen given identical? check)
        :else
        (mk-eq-refl st lhs)))))
