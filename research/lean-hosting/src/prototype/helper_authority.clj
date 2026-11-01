(ns prototype.helper-authority
  "Validate executable helper closures against current independent authority.
   Returned identity snapshots authorize only the supplied helper invocation
   boundary; they establish no kernel checking or artifact admission history."
  (:require [prototype.eval-const :as eval]))

(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))

(defn check
  "Validate current independent function/binding authority for ROOTS, then
   require exact closure identity against EXPECTED when supplied. Returns the
   actual function/binding snapshot without executing guest code."
  [context world roots expected]
  (require! (and (fn? (:invoke context)) (map? (:trusted-functions context)))
            "Current authorized helper invoker and independent registry required" {})
  (require! (and (vector? roots) (every? vector? roots)) "Explicit guest helper targets required" {})
  (loop [pending roots functions {} bindings {}]
    (if (empty? pending)
      (let [actual {:functions functions :bindings bindings}]
        (when expected
          (require! (and (= (set (keys functions)) (set (keys (:functions expected))))
                         (= (set (keys bindings)) (set (keys (:bindings expected))))
                         (every? (fn [[name value]] (identical? value (get-in expected [:functions name]))) functions)
                         (every? (fn [[name value]] (identical? value (get-in expected [:bindings name]))) bindings))
                    "Checked base protected helper closure changed" {}))
        actual)
      (let [name (peek pending) pending (pop pending)]
        (if (contains? functions name) (recur pending functions bindings)
          (let [function (get-in world [:functions name])
                _ (require! (and (map? function) (identical? function (get (:trusted-functions context) name)))
                            "Checked base helper executable identity changed" {:name name})
                symbol (get-in function [:raw-extern :symbol])
                binding (when symbol (get (:bindings context) symbol))]
            (when symbol
              (require! (and binding (identical? binding (get (:trusted-bindings context) symbol)))
                        "Checked helper binding lacks independent identity authority" {:symbol symbol}))
            (recur (into pending (eval/executable-dependencies function))
                   (assoc functions name function) (cond-> bindings symbol (assoc symbol binding)))))))))

(defn capture
  "Capture the current independently authorized helper closure identities.
   Executes no guest code and issues no kernel admission capability."
  [context world roots]
  (check context world roots nil))
