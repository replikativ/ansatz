(ns prototype.scoped-projector-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.machine :as m]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as guest]
            [prototype.imported-kernel :as imported]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo Expr]))

(defn- axiom [world text type]
  (let [[world n] (guest/guest-name world text)
        [world base] (guest/ctor world 0 [n guest/nil-tag type] 0)
        [world payload] (guest/ctor world 0 [base] 1)]
    (guest/ctor world 0 [payload] 0)))
(defn- constants-with-shared-expressions []
  (let [[w prop] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        [w succ] (guest/ctor w 1 [guest/nil-tag] 8)
        [w type] (guest/ctor w 3 [succ] 8)
        w (m/retain w prop 2)
        [w p] (axiom w "P" prop)
        [w q] (axiom w "Q" prop)
        [w n] (guest/guest-name w "T")
        w (m/retain w n 1)
        [w base] (guest/ctor w 0 [n guest/nil-tag type] 0)
        [w all] (guest/ctor w 1 [n guest/nil-tag] 0)
        [w payload] (guest/ctor w 0 [base prop guest/nil-tag all] 1)
        w (guest/scalar! w payload 0 "uint8" 1)
        [w t] (guest/ctor w 1 [payload] 0)]
    [w [p q t]]))

(deftest bulk-verification-shares-ci-types-and-definition-body-without-guest-effects
  (let [[world refs] (constants-with-shared-expressions)
        before world
        certificate (imported/verify-constants world refs {:allow-axioms? true})
        projected (:projected certificate)
        ^ConstantInfo p (get projected (name/from-string "P"))
        ^ConstantInfo q (get projected (name/from-string "Q"))
        ^ConstantInfo t (get projected (name/from-string "T"))]
    (is (= 3 (count projected)))
    (is (identical? (.type p) (.type q)))
    (is (identical? (.type p) (.value t)))
    (is (not (identical? (.type t) (.value t))))
    (is (identical? world before))
    (is (= 3 (:rc (m/node world (m/->Ref 0)))))
    (is (empty? (:heap (reduce #(m/release %1 %2 1) world refs))))))

(deftest explicit-projector-context-and-fresh-default-are-distinct
  (let [[world root] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        scoped (bridge/make-projector world)
        a (bridge/project-with-stats world :expr root scoped)
        b (bridge/project-with-stats world :expr root scoped)
        fresh1 (bridge/project-expr world root)
        fresh2 (bridge/project-expr world root)]
    (is (identical? (:value a) (:value b)))
    (is (= (:projected-nodes a) (:projected-nodes b)))
    (is (not (identical? fresh1 fresh2)))
    (is (not (identical? (:value a) fresh1)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
                         (bridge/project-with-stats (into {} world) :expr root scoped))))
  (let [[first-world root] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        [second-world u] (guest/ctor first-world 1 [guest/nil-tag] 8)
        second-world (assoc-in second-world [:heap (:id root) :fields] [u])
        first-context (bridge/make-projector first-world)
        second-context (bridge/make-projector second-world)
        ^Expr a (bridge/project-expr first-world root first-context)
        ^Expr b (bridge/project-expr second-world root second-context)]
    (is (not= (.o0 a) (.o0 b)))
    (is (identical? a (bridge/project-expr first-world root first-context)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
                         (bridge/project-expr second-world root first-context)))))

(deftest scope-failures-do-not-suppress-layout-cycle-or-closedness-checks
  (let [[world good] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        [world malformed] (guest/ctor world 5 [] 8)
        [world cyclic] (guest/ctor world 5 [good good] 8)
        world (assoc-in world [:heap (:id cyclic) :fields 0] cyclic)
        [world loose] (guest/ctor world 0 [0] 8)
        scoped (bridge/make-projector world)
        ^Expr expected (bridge/project-expr world good scoped)]
    (dotimes [_ 2]
      (is (thrown? clojure.lang.ExceptionInfo (bridge/project-expr world malformed scoped)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cyclic" (bridge/project-expr world cyclic scoped))))
    (is (identical? expected (bridge/project-expr world good scoped)))
    ;; The raw Expr can legitimately be projected, but using its cached result as
    ;; a CLOSED expression must still run the public closedness guard every time.
    (is (= 1 (.bvarRange ^Expr (:value (bridge/project-with-stats world :expr loose scoped)))))
    (dotimes [_ 2]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Loose bound"
                           (bridge/project-expr world loose scoped))))))

(deftest mutable-constructor-fields-cannot-enter-a-world-scoped-memo
  (let [[world root] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        world (assoc-in world [:heap (:id root) :fields] (object-array [guest/nil-tag]))
        scoped (bridge/make-projector world)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"layout"
                         (bridge/project-expr world root scoped)))))
