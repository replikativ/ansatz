(ns ansatz.lean.jvm.host
  "Private typed host adapters. Does not admit imports or register Project code."
  (:require [ansatz.lean.jvm.typed-value :as typed])
  (:import [java.util.function Function]))

(defn clojure-implementation
  "Capture one IFn target; authenticated import admission supplies the types.
   Capturing a Var's current value does not freeze dependencies or captures."
  [argument-types result-type implementation]
  (let [target (if (instance? clojure.lang.Var implementation) @implementation implementation)
        types (vec argument-types)]
    (when-not (instance? clojure.lang.IFn target)
      (throw (IllegalArgumentException. "Expected an actual Clojure function")))
    (reify Function
      (apply [_ arguments]
        (when-not (= (count types) (count arguments))
          (throw (IllegalArgumentException. "Host argument count differs from admitted signature")))
        (typed/host-value result-type
                          (apply target (mapv typed/view types arguments)))))))
