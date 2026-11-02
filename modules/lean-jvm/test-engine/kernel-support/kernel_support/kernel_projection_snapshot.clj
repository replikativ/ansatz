(ns kernel-support.kernel-projection-snapshot
  "Complete eager Java projection and mutable-container correspondence guards.
   These snapshots grant no strict checking, artifact admission, guest
   association, or helper invocation authority. Hosts serialize Java mutation."
  (:require [kernel-support.imported-kernel :as imported])
  (:import [ansatz.kernel Env ConstantInfo ConstantInfo$RecursorRule Expr]
           [java.util IdentityHashMap]))

(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))

(defn ^:no-doc validate-eager-domain [certificate]
  (let [^Env checked (:env certificate) constants (:constants certificate) projected (:projected certificate)]
    (require! (and (instance? Env checked) (map? constants) (map? projected))
              "Actual strict verifier certificate required" {})
    (require! (.sameExternalView checked (Env.)) "Lazy/external checked bases are unsupported" {})
    (let [actual (into {} (map #(vector (.name ^ConstantInfo %) %) (.allConstants checked)))]
      (require! (= (set (keys constants)) (set (keys projected)) (set (keys actual)))
                "Checked base has incomplete Java ConstantInfo domain" {})
      (doseq [[name ^ConstantInfo ci] projected]
        (require! (and (instance? ConstantInfo ci) (= name (.name ci))
                       (identical? ci (get actual name)) (identical? ci (.lookup checked name)))
                  "Certificate projection differs from actual checked Env" {:name name})))
    certificate))

(defn ^:no-doc expression-array-witnesses [certificate]
  ;; Typed bridge Expr fields are final, but CONST universe arguments may be
  ;; Java arrays. Keep only those mutable-container witnesses; share the DAG.
  (let [seen (IdentityHashMap.) arrays (IdentityHashMap.)
        roots (mapcat (fn [^ConstantInfo ci]
                        (concat [(.type ci) (.value ci)]
                                (when (.isRecursor ci)
                                  (map #(.rhs ^ConstantInfo$RecursorRule %) (.rules ci)))))
                      (vals (:projected certificate)))]
    (loop [pending (vec (remove nil? roots)) witnesses []]
      (if (empty? pending) witnesses
        (let [^Expr e (peek pending) pending (pop pending)]
          (if (.containsKey seen e) (recur pending witnesses)
            (do
              (.put seen e true)
              (let [levels (when (= Expr/CONST (.tag e)) (.o1 e))
                    array? (instance? (class (object-array 0)) levels)
                    fresh? (and array? (not (.containsKey arrays levels)))
                    _ (when fresh? (.put arrays levels true))
                    children (case (.tag e)
                               3 [(.o0 e) (.o1 e)]
                               (4 5) [(.o1 e) (.o2 e)]
                               6 [(.o1 e) (.o2 e) (.o3 e)]
                               (9 10) [(.o1 e)]
                               [])]
                (recur (into pending children)
                       (cond-> witnesses fresh? (conj [levels (mapv identity levels)])))))))))))

(defn- current-java-base! [certificate]
  ;; Env maps are persistent, but ConstantInfo exposes mutable Java fields.
  ;; Validate the objects actually used by the checker as well as guest data.
  ;; The owning host must still prohibit concurrent mutation during an operation.
  (validate-eager-domain certificate)
  (doseq [[name ^ConstantInfo ci] (:projected certificate)]
    (require! (= (get (:shapes certificate) name) (imported/checking-shape ci))
              "Inherited Java ConstantInfo checking shape changed" {:name name}))
  (doseq [[levels captured] (:expression-arrays certificate)]
    (require! (= captured (mapv identity levels))
              "Inherited Java expression universe array changed" {})))

(defn ^:no-doc snapshot-projection
  "Capture mutable Java containers in a complete eager projection.
   This is correspondence evidence only: it grants no checking or artifact
   admission authority. The owning host prevents concurrent mutation."
  [projection]
  (validate-eager-domain projection)
  (assoc projection
         :shapes (into {} (map (fn [[name ci]] [name (imported/checking-shape ci)]))
                       (:projected projection))
         :expression-arrays (expression-array-witnesses projection)))

(defn ^:no-doc validate-projection
  "Compare actual eager Java objects with captured container snapshots.
   Does not authenticate the projection or establish checking history."
  [snapshot]
  (current-java-base! snapshot)
  snapshot)

(defn ^:no-doc snapshot-segment
  "Snapshot only a newly checked group, without enumerating its inherited Env.
   Captured objects remain borrowed; no admission authority is created."
  [projected]
  (require! (and (map? projected)
                 (every? (fn [[name ci]] (and (instance? ConstantInfo ci)
                                              (= name (.name ^ConstantInfo ci)))) projected))
            "Explicit Java ConstantInfo group required" {})
  {:projected projected
   :shapes (into {} (map (fn [[name ci]] [name (imported/checking-shape ci)])) projected)
   :expression-arrays (expression-array-witnesses {:projected projected})})

(defn ^:no-doc validate-segment-values
  "Check captured CI/container values only; never call Env.lookup or enumerate
   a domain. Safe inside a private guarded lazy lookup. Grants no authority."
  [segment]
  (require! (map? (:projected segment)) "Captured Java group witnesses required" {})
  (doseq [[name ^ConstantInfo ci] (:projected segment)]
    (require! (= (get (:shapes segment) name) (imported/checking-shape ci))
              "Inherited Java ConstantInfo checking shape changed" {:name name}))
  (doseq [[levels captured] (:expression-arrays segment)]
    (require! (= captured (mapv identity levels))
              "Inherited Java expression universe array changed" {}))
  segment)

(defn ^:no-doc validate-segment
  "Check one group's witnesses against the current Env, without a base scan."
  [^Env environment segment]
  (require! (and (instance? Env environment) (map? (:projected segment)))
            "Java Env and captured group witnesses required" {})
  (doseq [[name ^ConstantInfo ci] (:projected segment)]
    (require! (identical? ci (.lookup environment name))
              "Java witness differs from actual Env declaration" {:name name}))
  (validate-segment-values segment))

(defn ^:no-doc validate-segments
  "Audit complete eager Env witnesses at an explicit admission/recapture boundary.
   Callbacks preserve old segments and validate only newly checked groups."
  [^Env environment segments]
  (require! (vector? segments) "Explicit Java witness segments required" {})
  (let [projected (reduce (fn [out segment]
                            (validate-segment environment segment)
                            (doseq [name (keys (:projected segment))]
                              (require! (not (contains? out name))
                                        "Overlapping Java witness segments" {:name name}))
                            (into out (:projected segment))) {} segments)]
    (validate-eager-domain {:env environment :projected projected
                            :constants (zipmap (keys projected) (repeat nil))}))
  segments)
