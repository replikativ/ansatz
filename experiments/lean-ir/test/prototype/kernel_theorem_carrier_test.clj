(ns prototype.kernel-theorem-carrier-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as guest]
            [prototype.kernel-declaration-test :as source]
            [prototype.imported-kernel :as imported]
            [prototype.machine :as m]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel ConstantInfo Env Expr KernelAbort]))

(defn dependent-theorem []
  ;; Constructed layout test, not an original Lean compiler body:
  ;; theorem carrierIdentity : (P : Prop) -> P -> P := fun P h => h
  (let [[world prop] (guest/ctor (m/world {}) 3 [guest/nil-tag] 8)
        [world p] (guest/guest-name world "P")
        [world h] (guest/guest-name world "h")
        [world b0] (guest/ctor world 0 [0] 8)
        [world b1] (guest/ctor world 0 [1] 8)
        [world inner-type] (guest/ctor world 7 [h b0 b1] 9)
        [world type] (guest/ctor world 7 [p prop inner-type] 9)
        [world inner-proof] (guest/ctor world 6 [h b0 b0] 9)
        [world proof] (guest/ctor world 6 [p prop inner-proof] 9)
        [world n] (guest/guest-name world "carrierIdentity")
        [world peer] (guest/guest-name world "peer")
        [world all] (source/guest-list world [peer n peer])
        [world constant] (guest/ctor world 0 [n guest/nil-tag type] 0)
        [world theorem] (guest/ctor world 0 [constant proof all] 0)
        [world declaration] (guest/ctor world 2 [theorem] 0)]
    {:world world :declaration declaration :theorem theorem :constant constant
     :proof proof :type type :prop prop :all all}))

(defn alternate-carrier [world]
  ;; Every reference is replaced, so any accidental m/node or m/ref? use fails.
  (let [token (fn [value] (if (m/ref? value) [:foreign (:id value)] value))
        nodes (into {} (map (fn [[id node]]
                             [[:foreign id] (update node :fields #(mapv token %))]) (:heap world)))
        carrier (Object.)]
    {:world carrier :token token
     :ops {:ref? #(and (vector? %) (= :foreign (first %)))
           :node (fn [current value]
                   (assert (identical? carrier current))
                   (or (get nodes value) (throw (ex-info "Unknown foreign reference" {}))))}}))

(deftest dependent-theorem-checks-on-both-carriers-with-complete-metadata
  (let [{:keys [world declaration]} (dependent-theorem)
        alternate (alternate-carrier world)]
    (doseq [[current root projector]
            [[world declaration (bridge/make-projector world)]
             [(:world alternate) ((:token alternate) declaration)
              (bridge/make-projector (:world alternate) (:ops alternate))]]]
      (let [before (Env.)
            result (bridge/admit-theorem current before root 1000000 projector)
            ^ConstantInfo constant (:constant result)]
        (is (= ConstantInfo/THM (.tag constant)))
        (is (= ["peer" "carrierIdentity" "peer"] (mapv str (.all constant))))
        (is (= Expr/LAM (.tag ^Expr (.value constant))))
        (is (false? (.isUnsafeDeclaration constant)))
        (is (identical? current (:world result)))
        (is (= root (:guest-declaration result)))
        (is (nil? (.lookup before (name/from-string "carrierIdentity"))))
        (is (identical? constant (.lookup ^Env (:env result) (.name constant))))
        (is (thrown? Exception (bridge/admit-theorem current (:env result) root 1000000 projector)))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
              (bridge/admit-theorem (Object.) before root 1000000 projector)))))))

(deftest authentic-pinned-native-theorem-uses-carrier-parametric-admission
  ;; Existing native-produced fixture/source pin; no rewritten Lean theorem.
  (let [{:keys [world values] :as fixture} (source/fixture)
        root (get values "identityProof") before (source/base-env fixture)
        alternate (alternate-carrier world)]
    (doseq [[current declaration projector]
            [[world root (bridge/make-projector world)]
             [(:world alternate) ((:token alternate) root)
              (bridge/make-projector (:world alternate) (:ops alternate))]]]
      (let [^ConstantInfo expected (imported/project-constant world root)
            ^ConstantInfo actual (:constant (bridge/admit-theorem current before declaration 1000000 projector))]
        (is (= (.name expected) (.name actual)))
        (is (= (vec (.levelParams expected)) (vec (.levelParams actual))))
        (is (= (vec (.all expected)) (vec (.all actual))))
        (is (= (.value expected) (.value actual)))
        (is (= (.type expected) (.type actual)))))))

(deftest invalid-proof-type-and-unresolved-terms-never-add-a-name
  (let [{:keys [world declaration theorem constant prop]} (dependent-theorem)
        [world missing] (guest/constant world "Missing")
        [world mvar] (guest/ctor world 2 [guest/nil-tag] 8)
        [world level-mvar] (guest/ctor world 5 [guest/nil-tag] 8)
        [world unresolved-sort] (guest/ctor world 3 [level-mvar] 8)
        before (Env.)]
    (doseq [invalid [(assoc-in world [:heap (:id theorem) :fields 1] prop)
                     (assoc-in world [:heap (:id constant) :fields 2] missing)
                     (assoc-in world [:heap (:id constant) :fields 2] prop)
                     (assoc-in world [:heap (:id theorem) :fields 1] mvar)
                     (assoc-in world [:heap (:id constant) :fields 2] unresolved-sort)]]
      (let [alternate (alternate-carrier invalid)]
        (is (thrown? Exception (bridge/admit-theorem invalid before declaration)))
        (is (thrown? Exception
              (bridge/admit-theorem (:world alternate) before ((:token alternate) declaration)
                1000000 (bridge/make-projector (:world alternate) (:ops alternate)))))))
    (is (nil? (.lookup before (name/from-string "carrierIdentity"))))
    (is (= 6 (:tag (m/node world (second (:fields (m/node world theorem)))))))))

(deftest malformed-layout-and-name-list-reject-before-admission
  (let [{:keys [world declaration theorem all]} (dependent-theorem)
        before (Env.)]
    (doseq [invalid [(assoc-in world [:heap (:id declaration) :tag] 1)
                     (assoc-in world [:heap (:id theorem) :fields] [theorem all])
                     (assoc-in world [:heap (:id theorem) :layout] {:objects 3 :usize 0 :ssize 1})
                     (assoc-in world [:heap (:id all) :tag] 2)
                     (assoc-in world [:heap (:id all) :fields 1] all)]]
      (is (thrown? clojure.lang.ExceptionInfo (bridge/admit-theorem invalid before declaration))))
    (is (nil? (.lookup before (name/from-string "carrierIdentity"))))))

(deftest checking-fuel-and-carrier-budget-are-enforced-including-memo-hits
  (let [{:keys [world declaration constant type prop]} (dependent-theorem)
        before (Env.) alternate (alternate-carrier world)
        remaining (atom 10000)
        ops (assoc (:ops alternate) :check!
              (fn [] (when (neg? (swap! remaining dec)) (throw (ex-info "Projection budget exhausted" {})))))
        projector (bridge/make-projector (:world alternate) ops)
        root ((:token alternate) declaration)]
    (doseq [fuel [0 -1 1.5 9223372036854775808N]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fuel"
            (bridge/admit-theorem world before declaration fuel))))
    ;; Fuel bounds reductions, not expression visits. The plain identity proof
    ;; needs no beta reduction; force four in its declared proposition instead:
    ;; (fun P : Prop => P) (... ((fun P : Prop => P) identityType)).
    (let [[reduction-world binder] (guest/guest-name world "betaP")
          [reduction-world bound] (guest/ctor reduction-world 0 [0] 8)
          [reduction-world identity] (guest/ctor reduction-world 6 [binder prop bound] 9)
          [reduction-world reduced-type]
          (loop [n 4 current-world reduction-world current type]
            (if (zero? n) [current-world current]
              (let [[next-world next-type] (guest/ctor current-world 5 [identity current] 8)]
                (recur (dec n) next-world next-type))))
          reduction-world (assoc-in reduction-world [:heap (:id constant) :fields 2] reduced-type)]
      (is (some? (:env (bridge/admit-theorem reduction-world before declaration 1000000))))
      (is (thrown-with-msg? KernelAbort #"fuel exhausted"
            (bridge/admit-theorem reduction-world before declaration 1))))
    (reset! remaining 2)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Projection budget"
          (bridge/admit-theorem (:world alternate) before root 1000000 projector)))
    (reset! remaining 10000)
    (is (some? (:env (bridge/admit-theorem (:world alternate) before root 1000000 projector))))
    (reset! remaining 0)
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Projection budget"
          (bridge/admit-theorem (:world alternate) before root 1000000 projector)))
    (is (nil? (.lookup before (name/from-string "carrierIdentity"))))))
