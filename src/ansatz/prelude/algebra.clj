(ns ansatz.prelude.algebra
  "The owned algebraic spine of the verified-data-pipeline foundation: WAddMonoid ⊂ WSemiring,
   bundled-axiom typeclasses over ansatz's `a/structure :extends` (the Lean-4 packed-subobject model).

   This is the ONE genuinely-custom piece of the foundation. The List fusion lemmas
   (List.map_map / foldl_map / filter_filter / *_cons / map_flatMap / sum_append) come FREE from the
   Init store; only the semiring algebra — which is Mathlib-only in Lean — is ours. The fragment is
   non-unital, non-commutative, left-distributive: exactly what the FAQ frame / aggregation laws need,
   leaner than Mathlib's `Semiring`.

       WAddMonoid S = { add, zero, add_assoc, zero_add, add_zero }              -- aggregation monoid
       WSemiring  S extends WAddMonoid + { mul, mul_add, mul_zero, zero_mul }   -- + left-distributive product

   `install-classes!` defines the classes into the (initialised) ansatz env. Instances are built
   straight from a carrier's ops + axiom-proof lemma names; the kernel checks the proofs line up
   (e.g. mul_add's `add` reduces through the subobject projection to the carrier's add by defeq).

   Companion plan: ansatz/docs/WANDLER_REIMPL_PLAN.md (Pillar B). Rebuilt clean from the wandler
   reference `wandler.semiring-class`."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]))

(defn- kconst [s] (e/const' (nm/from-string s) []))
(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))

(defn classes-installed? []
  (and (has? "WAddMonoid") (has? "WSemiring")))

(defn install-classes!
  "Define WAddMonoid ⊂ WSemiring into the current ansatz env (idempotent). Requires an initialised
   env (a/init! / load-init! / reset! ansatz-env)."
  []
  (when-not (classes-installed?)
    (eval '(ansatz.core/structure WAddMonoid [S Type]
             (add (=> S S S)) (zero S)
             (add_assoc (forall [a S b S c S] (= S (add (add a b) c) (add a (add b c)))))
             (zero_add (forall [a S] (= S (add zero a) a)))
             (add_zero (forall [a S] (= S (add a zero) a)))))
    (eval '(ansatz.core/structure WSemiring [S Type] :extends (WAddMonoid S)
             (mul (=> S S S))
             (mul_add (forall [a S b S c S] (= S (mul a (add b c)) (add (mul a b) (mul a c)))))
             (mul_zero (forall [a S] (= S (mul a zero) zero)))
             (zero_mul (forall [a S] (= S (mul zero a) zero))))))
  :installed)

;; ── Instance terms (carrier-agnostic; from an ops+proof-name row) ────────────────────────────
;; A `row` maps each carrier op (:add :zero :mul) and each axiom proof
;; (:add_assoc :zero_add :add_zero :mul_add :mul_zero :zero_mul) to a kernel const NAME (string).
;; `S` is a kernel const term, e.g. `(e/const' (name/from-string "Nat") [])`.

(defn addmonoid-instance
  "WAddMonoid.mk S add zero add_assoc zero_add add_zero — a `WAddMonoid S` term."
  [S row]
  (e/app* (kconst "WAddMonoid.mk") S
          (kconst (:add row)) (kconst (:zero row))
          (kconst (:add_assoc row)) (kconst (:zero_add row)) (kconst (:add_zero row))))

(defn semiring-instance
  "WSemiring.mk S <WAddMonoid inst> mul mul_add mul_zero zero_mul — a `WSemiring S` term (the parent
   instance built inline, like Lean's subobject constructor)."
  [S row]
  (e/app* (kconst "WSemiring.mk") S
          (addmonoid-instance S row)
          (kconst (:mul row)) (kconst (:mul_add row)) (kconst (:mul_zero row)) (kconst (:zero_mul row))))

(def nat-row
  "The WSemiring instance row for Nat, from Init lemmas. Uses `Nat.left_distrib` for mul_add (present
   in init-medium; `Nat.mul_add` is the full-store synonym)."
  {:add "Nat.add" :zero "Nat.zero" :mul "Nat.mul"
   :add_assoc "Nat.add_assoc" :zero_add "Nat.zero_add" :add_zero "Nat.add_zero"
   :mul_add "Nat.left_distrib" :mul_zero "Nat.mul_zero" :zero_mul "Nat.zero_mul"})

(defn install-instance!
  "Build and KERNEL-VERIFY the WAddMonoid + WSemiring instances for `carrier` (a kernel const name,
   e.g. \"Nat\") from `row`, adding both to the env as `instWAddMonoid_<carrier>` /
   `instWSemiring_<carrier>`. Returns a status map; on any missing lemma or proof mismatch the kernel
   rejects it and we report :failed without mutating further (the gate cannot be fooled)."
  [carrier row]
  (install-classes!)
  (let [S (kconst carrier)
        am-name (str "instWAddMonoid_" carrier)
        ws-name (str "instWSemiring_" carrier)]
    (try
      (reset! a/ansatz-env
              (env/check-constant (a/env)
                                  (env/mk-def (nm/from-string am-name) []
                                              (e/app (kconst "WAddMonoid") S)
                                              (addmonoid-instance S row))))
      (reset! a/ansatz-env
              (env/check-constant (a/env)
                                  (env/mk-def (nm/from-string ws-name) []
                                              (e/app (kconst "WSemiring") S)
                                              (e/app* (kconst "WSemiring.mk") S (kconst am-name)
                                                      (kconst (:mul row)) (kconst (:mul_add row))
                                                      (kconst (:mul_zero row)) (kconst (:zero_mul row))))))
      {:carrier carrier :status :verified :addmonoid am-name :semiring ws-name}
      (catch Exception ex
        {:carrier carrier :status :failed :error (.getMessage ex)}))))
