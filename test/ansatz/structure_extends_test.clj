(ns ansatz.structure-extends-test
  "Lean-4-faithful structure inheritance (`:extends`) — the packed `subobject` model.
   See docs/EXTENDS_DESIGN.md. Covers: the parent embeds as a `to{Parent}` field (projection
   free), inherited accessors are generated, child axioms may reference parent ops (resolved to
   subobject projections, Lean's `fromSubobject`), and BOTH levels admit verified instances with
   the child built compositionally from the parent instance (the distributivity proof checks
   through the subobject projection by defeq)."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as nm]
            [ansatz.kernel.expr :as e]))

(def ^:private init-env test-env/checked-bundled-init-env)

(defn- with-init-env [f]
  (reset! a/ansatz-env @init-env)
  (f))

(clojure.test/use-fixtures :once with-init-env)

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

(deftest class-parent-projection-is-an-instance
  (let [saved (a/env)]
    (try
      (a/class ParentOps [S Type] (zero S))
      (a/class ChildOps [S Type] :extends (ParentOps S) (one S))
      (a/class GrandchildOps [S Type] :extends (ChildOps S) (two S))
      (a/structure PlainChild [S Type] :extends (ParentOps S) (one S))
      (a/structure PlainParent [S Type] (zero S))
      (a/class ClassOverPlain [S Type] :extends (PlainParent S) (one S))
      (let [entries (get (env/get-extension (a/env) :instances {}) (nm/from-string "ParentOps"))]
        (is (some #(and (= (nm/from-string "ChildOps.toParentOps") (:name %))
                        (= 1000 (:priority %))) entries))
        (is (not-any? #(= (nm/from-string "PlainChild.toParentOps") (:name %)) entries)))
      (is (empty? (get (env/get-extension (a/env) :instances {}) (nm/from-string "PlainParent"))))
      (a/theorem inherited-parent [S :- Type, child :- (GrandchildOps S) :inst]
                 (= (ParentOps S) (ChildOps.toParentOps (GrandchildOps.toChildOps child))
                    (ChildOps.toParentOps (GrandchildOps.toChildOps child)))
                 (rfl))
      ;; The body must synthesize the parent using only a grandchild local instance.
      (a/defn parent-zero [S :- Type, parent :- (ParentOps S) :inst] S
              (ParentOps.zero parent))
      (a/defn inherited-zero [S :- Type :implicit, child :- (GrandchildOps S) :inst] S
              (parent-zero S))
      (is (has? "inherited-zero"))
      (finally (reset! a/ansatz-env saved)))))

(deftest imported-class-parent-projection-is-an-instance
  (let [saved (a/env)]
    (try
      (a/load-init! :verify? true)
      (is (contains? (env/get-extension (a/env) :classes #{}) "BEq"))
      (a/class ExtendedBEq [S Type] :extends (BEq S) (extra S))
      (is (some #(= (nm/from-string "ExtendedBEq.toBEq") (:name %))
                (get (env/get-extension (a/env) :instances {}) (nm/from-string "BEq"))))
      (a/defn require-beq [S :- Type, dictionary :- (BEq S) :inst] (BEq S) dictionary)
      (a/defn inherited-beq [S :- Type, child :- (ExtendedBEq S) :inst] (BEq S)
              (require-beq S))
      (is (has? "inherited-beq"))
      (finally (reset! a/ansatz-env saved)))))

(deftest store-session-inherits-exported-class-identity
  (let [saved (a/env)]
    (try
      (a/load-init! :verify? true)
      (a/structure ExportedParent [S Type] (zero S))
      (let [index (select-keys (env/get-extension (a/env) :instances {}) [(nm/from-string "BEq")])
            prepared (#'a/prepare-proof-session (a/env) {:store-path "metadata-fixture" :branch "init"}
                       nil {:attrs [["class" "ExportedParent" nil nil]] :instances index :matchers {}})
            loaded (:env prepared)]
        (is (contains? (env/get-extension loaded :classes #{}) "BEq"))
        (is (contains? (env/get-extension loaded :classes #{}) "ExportedParent"))
        (reset! a/ansatz-env loaded))
      (a/class ExportedChild [S Type] :extends (ExportedParent S) (one S))
      (is (some #(= (nm/from-string "ExportedChild.toExportedParent") (:name %))
                (get (env/get-extension (a/env) :instances {}) (nm/from-string "ExportedParent"))))
      (finally (reset! a/ansatz-env saved)))))

(deftest imported-class-without-instances-registers-parent
  (let [saved (a/env)]
    (try
      (a/load-init! :verify? true)
      (is (contains? (env/get-extension (a/env) :classes #{}) "Ord"))
      (is (empty? (get (env/get-extension (a/env) :instances {}) (nm/from-string "Ord"))))
      (a/class ExtraOrd [S Type] :extends (Ord S) (extra S))
      (is (some #(= (nm/from-string "ExtraOrd.toOrd") (:name %))
                (get (env/get-extension (a/env) :instances {}) (nm/from-string "Ord"))))
      (a/defn require-ord [S :- Type, dictionary :- (Ord S) :inst] (Ord S) dictionary)
      (a/defn inherited-ord [S :- Type, child :- (ExtraOrd S) :inst] (Ord S)
              (require-ord S))
      (is (has? "inherited-ord"))
      (finally (reset! a/ansatz-env saved)))))
