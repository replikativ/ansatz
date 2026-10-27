(ns ansatz.storedef-test
  "Equation-driven runtime compilation of plain store defs (ansatz.codegen.storedef):
   a recursive store def compiles from its exported f.eq_def theorem into a Clojure fn
   with `recur` at tail self-calls, interned under its dotted Lean name in
   ansatz.storedef.runtime and registered {:arity :erased :sym} — which re-activates the
   csimp TR rewrites through the #62 lowerability guard. Store-backed cases skip
   gracefully when the booted store carries no equation lemmas."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.eqns :as eqns]
            [ansatz.codegen :as cg]
            [ansatz.codegen.storedef :as sd]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(defn- has-decl? [n] (some? (env/lookup (a/env) (name/from-string n))))

;; ── pure form-rewrite units (no store needed) ────────────────────────────────

(deftest form-beta-exposes-tail-positions
  (let [beta @#'sd/form-beta]
    (is (= '(let [x 1] x) (beta '((fn [x] x) 1))))
    (testing "application of a let (curried chain) pushes inside"
      (is (= '(let [x 1] (let [y 2] (f x y)))
             (beta '(((fn [x] (fn [y] (f x y))) 1) 2)))))))

(deftest rewrite-self-recur-vs-named
  (let [rw @#'sd/rewrite-self
        dsym (symbol "Fake.self")]
    (testing "tail self-call becomes recur, erased prefix stripped"
      (is (= '(if c 0 (recur t (inc n)))
             (rw (list 'if 'c 0 (list dsym 'A 't '(inc n))) dsym 'self_ 1 3))))
    (testing "self-call under an inner fn boundary takes the named call, never recur"
      (let [out (rw (list 'if 'c 0 (list 'fn '[k] (list dsym 'A 'k 'n))) dsym 'self_ 1 3)]
        (is (= '(if c 0 (fn [k] (self_ k n))) out))))
    (testing "non-tail self-call takes the named call"
      (is (= '(if c 0 (inc (self_ t n)))
             (rw (list 'if 'c 0 (list 'inc (list dsym 'A 't 'n))) dsym 'self_ 1 3))))
    (testing "arity-mismatched self-call fails the rewrite"
      (is (nil? (rw (list dsym 'A 't) dsym 'self_ 1 3))))))

;; ── store-backed integration (skips without exported equation lemmas) ────────

(deftest compile-recursive-store-def-with-recur
  (if-not (has-decl? "List.lengthTRAux.eq_def")
    (is true "store carries no equation lemmas — skipped")
    (let [entry (sd/compile-store-def! (a/env) "List.lengthTRAux")]
      (is (some? entry) "List.lengthTRAux compiles from its eq_def")
      (is (= 2 (:arity entry)))
      (is (= 1 (:erased entry)))
      (let [f @(resolve (:sym entry))]
        (is (= 3 (f [10 20 30] 0)))
        (testing "tail self-call became recur: depth far beyond the JVM stack"
          (is (= 100000 (f (range 100000) 0))))))))

(deftest compile-wrapper-and-cross-def-chain
  (if-not (has-decl? "List.reverseAux.eq_def")
    (is true "store carries no equation lemmas — skipped")
    (let [entry (sd/compile-store-def! (a/env) "List.reverse")]
      (is (some? entry) "non-recursive wrapper compiles via its value, worker via eq_def")
      (let [f @(resolve (:sym entry))]
        (is (= [3 2 1] (into [] (f [1 2 3]))))
        (is (= 100000 (count (f (range 100000)))))))))

(deftest codegen-fall-through-compiles-plain-store-head
  (if-not (has-decl? "List.lengthTRAux.eq_def")
    (is true "store carries no equation lemmas — skipped")
    (let [term (e/app* (e/const' (name/from-string "List.lengthTRAux") [lvl/zero])
                       (e/const' (name/from-string "Nat") []))
          code (cg/ansatz->clj (a/env) term [])]
      (is (some #(and (symbol? %) (= "ansatz.storedef.runtime" (namespace %)))
                (tree-seq coll? seq code))
          "plain store head lowered to the interned qualified var"))))

(deftest csimp-does-not-hijack-native-lowerings
  ;; List.length has a native `count` builtin; even with List.lengthTR compilable, the
  ;; csimp swap must keep the native lowering.
  (when (has-decl? "List.length")
    (let [csimp-t @#'cg/csimp-target]
      (is (nil? (csimp-t (a/env) "List.length"))))))

;; ── unified emitter: own a/defn (no store equations needed — runs everywhere) ─
;; An accumulator-style defn (self-call args CHANGE) fails the structural IH rewrite and
;; auto-routes to the WF path (GuessLex), so this exercises the wf.clj emitter wiring.

(deftest own-defn-tail-recursion-becomes-recur
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} sdt-len-acc [^{:- (List Nat)} xs ^{:- Nat} n]
      (match xs (List Nat) Nat
             (nil n)
             (cons [h t] (sdt-len-acc t (Nat.succ n)))))
    (is (= 3 (sdt-len-acc [1 2 3] 0)))
    (testing "tail-recursive accumulator defn runs at depths that overflowed the closure cascade"
      (is (= 100000 (sdt-len-acc (range 100000) 0))))
    (testing "registry entry carries :surface provenance"
      (is (= :surface (:provenance (get @ansatz.surface.ingest/arity-registry "sdt-len-acc")))))
    (testing "curried value-position call style still works"
      (is (= 4 ((sdt-len-acc [1 2 3]) 1))))))

(deftest own-defn-non-tail-still-correct
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} sdt-len [^{:- (List Nat)} xs]
      (match xs (List Nat) Nat
             (nil Nat.zero)
             (cons [h t] (Nat.succ (sdt-len t)))))
    (is (= 3 (sdt-len [1 2 3])))
    (is (= 5000 (sdt-len (range 5000))) "non-tail recursion stays correct (stack-bound as before)")))

;; ── long literals + promoting arithmetic ─────────────────────────────────────

(deftest nat-literals-emit-longs-and-arithmetic-promotes
  (binding [a/*verbose* false]
    (a/defn ^{:- Nat} sdt-add3 [^{:- Nat} k] (Nat.add k 3))
    (testing "literal-seeded arithmetic stays primitive long"
      (is (instance? Long (sdt-add3 4)))
      (is (= 7 (sdt-add3 4))))
    (a/defn ^{:- Nat} sdt-sq [^{:- Nat} k] (Nat.mul k k))
    (testing "overflow promotes to bigint (unbounded Nat semantics) instead of throwing"
      (let [big (long (Math/pow 2 40))
            r (sdt-sq big)]
        (is (= (*' big big) r))))))

(deftest kill-switch-restores-old-behavior
  (binding [cg/*compile-store-defs* false]
    (when (has-decl? "List.lengthTRAux.eq_def")
      (sd/reset-cache!)
      ;; with the switch off, nothing new lands in the runtime ns via codegen fall-through
      (let [term (e/app* (e/const' (name/from-string "List.eraseIdxTR") [lvl/zero])
                         (e/const' (name/from-string "Nat") []))
            code (cg/ansatz->clj (a/env) term [])]
        (is (not-any? #(and (symbol? %) (= "ansatz.storedef.runtime" (namespace %)))
                      (tree-seq coll? seq code)))))))

(deftest unsupported-store-definition-reports-reason-without-poisoning-search
  (let [nm (name/from-string "RuntimeIdentity")
        nat (e/const' (name/from-string "Nat") [])
        ty (e/forall "x" nat nat :default)
        good (env/mk-def nm [] ty (e/lam "x" nat (e/bvar 0) :default) :hints {:regular 1})
        bad (env/mk-def (name/from-string "RuntimeUnsupported") [] ty
                       (e/lam "x" nat (e/const' (name/from-string "Nat.brecOn") []) :default)
                       :hints {:regular 1})
        en (-> (a/env) (env/add-constant good) (env/add-constant bad))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"RuntimeUnsupported.*Nat.brecOn.*equation"
                          (sd/compile-store-def! en "RuntimeUnsupported")))
    (let [entry (sd/compile-store-def! en "RuntimeIdentity")]
      (is (= 7 ((deref (resolve (:sym entry))) 7)))))
  (testing "a failed definition can compile after a runtime dependency becomes available"
    (let [nm (name/from-string "RuntimeRetry")
          dep (name/from-string "RuntimeDependency")
          nat (e/const' (name/from-string "Nat") [])
          ty (e/forall "x" nat nat :default)
          ci (env/mk-def nm [] ty (e/lam "x" nat (e/app (e/const' dep []) (e/bvar 0)) :default) :hints {:regular 1})
          en (env/add-constant (a/env) ci)
          saved @a/codegen-registry]
      (try
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"RuntimeRetry"
                              (sd/compile-store-def! en "RuntimeRetry")))
        (swap! a/codegen-registry assoc "RuntimeDependency"
               (fn [_ expr names]
                 (cg/ansatz->clj en (first (second (e/get-app-fn-args expr))) names)))
        ;; A long-lived REPL can retain the former compiler's negative cache.
        (swap! @#'sd/compiled assoc "RuntimeRetry" {:fail true})
        (let [entry (sd/compile-store-def! en "RuntimeRetry")]
          (is (= 8 ((deref (resolve (:sym entry))) 8))))
        (finally (reset! a/codegen-registry saved))))))

(deftest eta-contracted-store-value-keeps-full-runtime-arity
  (let [nat (e/const' (name/from-string "Nat") [])
        nm (name/from-string "RuntimeEtaSuccessor")
        ci (env/mk-def nm [] (e/forall "n" nat nat :default)
                       (e/const' (name/from-string "Nat.succ") []) :hints {:regular 1})
        entry (sd/compile-store-def! (env/add-constant (a/env) ci) "RuntimeEtaSuccessor")]
    (is (= 1 (:arity entry)))
    (is (= 8 ((deref (resolve (:sym entry))) 7)))))

(deftest recorded-equation-body-skips-inapplicable-equations
  (let [nat (e/const' (name/from-string "Nat") [])
        zero (e/lit-nat (biginteger 0))
        nm (name/from-string "RuntimeEquationBody")
        brec (env/lookup (a/env) (name/from-string "List.brecOn"))
        levels (vec (repeat (count (env/ci-level-params brec)) lvl/zero))
        brec-type (e/instantiate-level-params (.type brec) (zipmap (env/ci-level-params brec) levels))
        ;; Valid kernel term with an unused recursion encoding: compiling its
        ;; stored value is refused; its admitted direct equation must be used.
        ci (env/mk-def nm [] (e/forall "n" nat nat :default)
                       (e/lam "n" nat
                              (e/let' "unused" brec-type
                                      (e/const' (name/from-string "List.brecOn") levels) (e/bvar 1))
                              :default)
                       :hints {:regular 1})
        en (env/check-constant (a/env) ci)
        equation (fn [suffix arg]
                   (let [lhs (e/app (e/const' nm []) arg)
                         ty (e/forall "n" nat
                                      (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                                              nat lhs arg) :default)
                         proof (e/lam "n" nat
                                      (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                              nat arg) :default)]
                     (env/mk-thm (name/from-string (str "RuntimeEquationBody." suffix)) [] ty proof)))
        specific (equation "atZero" zero)
        general (equation "unfold" (e/bvar 0))
        en (-> en (env/check-constant specific) (env/check-constant general))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"RuntimeEquationBody.*List.brecOn"
                          (sd/compile-store-def! en "RuntimeEquationBody")))
    (let [en (eqns/register-eqn-thms en nm [(.name specific) (.name general)] [])
          entry (sd/compile-store-def! en "RuntimeEquationBody")]
      (is (= (.name general) (:equation entry)))
      (is (= 11 ((deref (resolve (:sym entry))) 11))))))

(deftest optional-store-candidate-records-refusal-before-other-lowerings
  (let [nat (e/const' (name/from-string "Nat") [])
        type0 (e/sort' (lvl/succ lvl/zero))
        c (fn [s] (e/const' (name/from-string s) [lvl/zero]))
        nm (name/from-string "ExplicitNumeralInstance")
        ci (env/mk-def nm []
                       (e/forall "alpha" type0
                                 (e/forall "n" nat (e/app* (c "OfNat") nat (e/bvar 0)) :default)
                                 :default)
                       (e/lam "alpha" type0
                              (e/lam "n" nat
                                     (e/app* (c "OfNat.mk") nat (e/bvar 0) (e/bvar 0)) :default)
                              :default)
                       :hints {:regular 1})
        en (env/check-constant (a/env) ci)
        two (e/lit-nat (biginteger 2))
        term (e/app* (c "OfNat.ofNat") nat two (e/app* (e/const' nm []) nat two))]
    (is (nil? (sd/try-compile-store-def! en "ExplicitNumeralInstance")))
    (is (= "ExplicitNumeralInstance" (:declaration (sd/failure-reason "ExplicitNumeralInstance"))))
    (is (re-find #"unsupported runtime binder telescope" (:reason (sd/failure-reason "ExplicitNumeralInstance"))))
    (testing "the numeric lowering follows the declined store candidate"
      (is (env/verifies? en
                        (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) nat term two)
                        (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) nat two)))
      (is (= 2 (eval (cg/ansatz->clj en term [])))))
    (testing "without a numeric lowering, the same refusal remains a hard named error"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"ExplicitNumeralInstance.*unsupported runtime binder telescope"
                            (cg/ansatz->clj en (e/app* (e/const' nm []) nat two) []))))))

(deftest optional-store-candidate-does-not-swallow-handler-errors
  (let [nat (e/const' (name/from-string "Nat") [])
        ty (e/forall "n" nat nat :default)
        dep (name/from-string "FaultyRuntimeHandler")
        ci (env/mk-def (name/from-string "RuntimeHandlerCaller") [] ty
                       (e/lam "n" nat (e/app (e/const' dep []) (e/bvar 0)) :default)
                       :hints {:regular 1})
        en (-> (a/env) (env/check-constant (env/mk-axiom dep [] ty)) (env/check-constant ci))
        original (env/mk-def (name/from-string "RuntimeHandlerOriginal") [] ty
                             (e/lam "n" nat (e/bvar 0) :default) :hints {:regular 1})
        en (-> en (env/check-constant original)
               (env/update-extension :csimp {} assoc "RuntimeHandlerOriginal" "RuntimeHandlerCaller"))
        failure (ex-info "runtime handler bug" {:kind :codegen-error})
        saved @a/codegen-registry]
    (try
      (swap! a/codegen-registry assoc "FaultyRuntimeHandler" (fn [& _] (throw failure)))
      (is (identical? failure
                      (try (sd/try-compile-store-def! en "RuntimeHandlerCaller")
                           (catch clojure.lang.ExceptionInfo ex ex))))
      (is (identical? failure
                      (try (cg/ansatz->clj en
                                          (e/app (e/const' (name/from-string "RuntimeHandlerOriginal") [])
                                                 (e/lit-nat (biginteger 5))) [])
                           (catch clojure.lang.ExceptionInfo ex ex))))
      (finally (reset! a/codegen-registry saved)))))
