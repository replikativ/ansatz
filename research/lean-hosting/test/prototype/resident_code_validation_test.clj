(ns prototype.resident-code-validation-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.resident-code-validation :as code])
  (:import [java.lang.ref WeakReference]
           [prototype.resident_code_validation CodeIdentityProof]))

(defn maps []
  (let [f (Object.) b (Object.)]
    [{"function" f} {"binding" b} {"function" f} {"binding" b}]))
(defn check [maps proof] (apply code/validate! (conj maps proof)))

(deftest hits-reuse-only-the-exact-validated-four-maps
  (let [maps (maps) proof (check maps nil)
        validator (ns-resolve 'prototype.resident-code-validation 'validate-mappings!)
        original @validator scans (atom 0)]
    (is proof)
    (with-redefs-fn {validator (fn [& args] (swap! scans inc) (apply original args))}
      #(do
         (is (every? (fn [candidate] (identical? proof candidate)) (repeatedly 100 (fn [] (check maps proof)))))
         (is (zero? @scans))
         (doseq [index (range 4)]
           (let [next-maps (update maps index with-meta {:new-image true})]
             (is (not (identical? proof (check next-maps proof))))))
         (is (= 4 @scans))))))

(deftest changed-mappings-and-unissued-proofs-cannot-bypass-validation
  (let [[functions bindings pf pb :as maps] (maps) proof (check maps nil)
        bad (assoc functions "function" (Object.))
        forged (CodeIdentityProof. (WeakReference. bad) (WeakReference. bindings)
                                   (WeakReference. pf) (WeakReference. pb))]
    (doseq [candidate [proof forged nil]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"protected executable"
                           (code/validate! bad bindings pf pb candidate))))
    (doseq [next-maps [(assoc maps 1 (assoc bindings "binding" (Object.)))
                      (assoc maps 2 (assoc pf "function" (Object.)))
                      (assoc maps 3 (assoc pb "binding" (Object.)))]]
      (is (thrown? clojure.lang.ExceptionInfo (check next-maps proof))))))

(deftest mutable-keys-and-custom-maps-use-the-uncached-path
  (let [[functions bindings pf pb] (maps)
        mutable-key (java.util.ArrayList. ["name"])]
    ;; An unrelated mutable key is enough to make the whole lookup map ineligible.
    (doseq [candidate [(assoc functions mutable-key :unrelated)
                       (into (sorted-map) functions)]]
      (is (nil? (code/validate! candidate bindings pf pb nil))))
    (is (nil? (code/validate! functions (assoc bindings mutable-key :unrelated) pf pb nil)))
    (let [f (Object.) expected {mutable-key f} actual {mutable-key f}]
      (is (nil? (code/validate! actual bindings expected pb nil)))
      (.set mutable-key 0 "changed")
      (is (nil? (code/validate! actual bindings expected pb nil))))))

(deftest hashed-mutable-keys-and-proof-epochs-never-grant-a-hit
  (let [[functions bindings pf pb :as maps] (maps)
        mutable-key (java.util.ArrayList. ["name"])
        actual (assoc (into functions (for [i (range 20)] [(str "padding" i) i])) mutable-key :unrelated)
        proof (check maps nil)]
    (is (= clojure.lang.PersistentHashMap (class actual)))
    (is (nil? (code/validate! actual bindings pf pb nil)))
    (.set mutable-key 0 "changed-hash")
    (is (nil? (code/validate! actual bindings pf pb nil)))
    (with-redefs-fn {(ns-resolve 'prototype.resident-code-validation 'issued) (java.util.WeakHashMap.)}
      #(is (not (identical? proof (check maps proof)))))))

(deftest proof-references-are-weak-and-clearing-them-forces-revalidation
  (let [[functions bindings pf pb :as maps] (maps) proof (check maps nil)]
    (doseq [reference [(.-functions ^CodeIdentityProof proof) (.-bindings ^CodeIdentityProof proof)
                       (.-protectedFunctions ^CodeIdentityProof proof) (.-protectedBindings ^CodeIdentityProof proof)]]
      (is (instance? WeakReference reference)))
    (.clear ^WeakReference (.-functions ^CodeIdentityProof proof))
    (is (not (identical? proof (check maps proof))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (code/validate! (assoc functions "function" (Object.)) bindings pf pb proof)))))
