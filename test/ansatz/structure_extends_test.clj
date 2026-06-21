(ns ansatz.structure-extends-test
  "Lean-4-faithful structure inheritance (`:extends`) — the packed `subobject` model.
   See docs/EXTENDS_DESIGN.md. Covers: the parent embeds as a `to{Parent}` field (projection
   free), inherited accessors are generated, child axioms may reference parent ops (resolved to
   subobject projections, Lean's `fromSubobject`), and BOTH levels admit verified instances with
   the child built compositionally from the parent instance (the distributivity proof checks
   through the subobject projection by defeq)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(defn- with-init-env [f]
  (when-let [env @init-env]
    (reset! a/ansatz-env env)
    (f)))

(use-fixtures :once with-init-env)

(defn- has? [s] (some? (env/lookup (a/env) (nm/from-string s))))
(defn- k [s] (e/const' (nm/from-string s) []))

(deftest extends-subobject-hierarchy
  (testing "WAddMonoid parent + WSemiring child via :extends, with verified Nat instances"
    (when @init-env
      (a/structure WAddMonoid [S Type]
                   (add (=> S S S)) (zero S)
                   (add_assoc (forall [a S b S c S] (= S (add (add a b) c) (add a (add b c)))))
                   (zero_add (forall [a S] (= S (add zero a) a)))
                   (add_zero (forall [a S] (= S (add a zero) a))))
      (a/structure WSemiring [S Type] :extends (WAddMonoid S)
                   (mul (=> S S S))
                   (mul_add (forall [a S b S c S] (= S (mul a (add b c)) (add (mul a b) (mul a c)))))
                   (mul_zero (forall [a S] (= S (mul a zero) zero)))
                   (zero_mul (forall [a S] (= S (mul zero a) zero))))

      ;; subobject field + its projection
      (is (has? "WSemiring.toWAddMonoid") "packed to{Parent} projection exists")
      ;; inherited accessors (Lean fromSubobject, materialized as abbrev defs)
      (is (and (has? "WSemiring.add") (has? "WSemiring.zero") (has? "WSemiring.add_assoc"))
          "inherited accessors generated")
      ;; own fields, incl. the cross-referencing distributivity axiom
      (is (and (has? "WSemiring.mul") (has? "WSemiring.mul_add")) "own fields generated")

      ;; verified instances — parent, then child built from the parent instance
      (let [NAT (k "Nat")
            amTy (e/app (k "WAddMonoid") NAT)
            instAM (e/app* (k "WAddMonoid.mk") NAT (k "Nat.add") (k "Nat.zero")
                           (k "Nat.add_assoc") (k "Nat.zero_add") (k "Nat.add_zero"))]
        (reset! a/ansatz-env
                (env/check-constant (a/env) (env/mk-def (nm/from-string "instWAddMonoidNat") [] amTy instAM)))
        (is (has? "instWAddMonoidNat") "WAddMonoid Nat instance kernel-verified")
        (let [wsTy (e/app (k "WSemiring") NAT)
              instWS (e/app* (k "WSemiring.mk") NAT (k "instWAddMonoidNat")
                             (k "Nat.mul") (k "Nat.left_distrib") (k "Nat.mul_zero") (k "Nat.zero_mul"))]
          ;; The distributivity proof Nat.left_distrib checks against mul_add's type whose `add`
          ;; reduces through WAddMonoid.add (the subobject projection) to Nat.add — by defeq.
          (reset! a/ansatz-env
                  (env/check-constant (a/env) (env/mk-def (nm/from-string "instWSemiringNat") [] wsTy instWS)))
          (is (has? "instWSemiringNat") "WSemiring Nat instance kernel-verified (through the subobject)"))))))

(deftest extends-rejects-multiple-parents
  (testing "multiple :extends parents are rejected (C3/copiedField path not yet implemented)"
    (is (thrown? Throwable
                 (eval '(a/structure Bad [S Type] :extends [(WAddMonoid S) (WOther S)]
                                     (x (=> S S S))))))))
