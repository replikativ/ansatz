(ns lean-compatibility-corpus
  "Non-executing inventory of pinned source/IR examples. Not a source loader."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [java-ir-baseline :as j]
            [prototype.import-ir :as ir])
  (:import [java.security MessageDigest]
           [java.math BigInteger]))

(defn sha256 [path]
  (let [digest (MessageDigest/getInstance "SHA-256")]
    (with-open [input (io/input-stream path)]
      (let [buffer (byte-array 8192)]
        (loop []
          (let [n (.read input buffer)]
            (when (pos? n) (.update digest buffer 0 n) (recur))))))
    (format "%064x" (BigInteger. 1 (.digest digest)))))

(defn failure [f]
  (try (f) nil
       (catch Exception e
         (loop [e e]
           (if-let [cause (ex-cause e)] (recur cause) (ex-message e))))))

(defn expression-calls [body]
  ;; Derive static calls from code, not the exporter's dependency metadata.
  (let [nodes (tree-seq coll? seq body)]
    {:static (into (sorted-set)
                   (keep (fn [node]
                           (when (map? node)
                             (when-let [call (or (get node "fap") (get node "pap"))]
                               (ir/name-label (get call "c")))))) nodes)
     :dynamic-sites (count (filter #(and (map? %) (contains? % "ap")) nodes))}))

(defn inventory [basis rows roots]
  (let [declarations (filter #(= "decl" (get % "kind")) rows)
        labels (map #(ir/name-label (get % "name")) declarations)
        _ (when (not= (count labels) (count (set labels)))
            (throw (ex-info "Duplicate/ambiguous declaration labels" {})))
        by-name (zipmap labels declarations)
        calls (into {} (map (fn [[label row]]
                             [label (expression-calls (get-in row ["ir" "fdecl" "body"]))])
                           by-name))
        required (loop [todo (vec roots) seen #{}]
                   (if-let [label (peek todo)]
                     (if (contains? seen label)
                       (recur (pop todo) seen)
                       (let [row (by-name label)
                             extra (keep identity [(get-in row ["runtime" "initializer"])
                                                   (get-in row ["redirect" "name"])])]
                         (recur (into (pop todo)
                                      (concat (get-in calls [label :static])
                                              (map ir/name-label extra)))
                                (conj seen label))))
                     seen))
        missing (vec (sort (remove by-name required)))
        selected (filter #(contains? required (ir/name-label (get % "name"))) declarations)
        externs (vec (sort-by :name
                             (for [row selected :let [ext (get-in row ["ir" "extern"])] :when ext]
                               {:name (ir/name-label (get row "name"))
                                :entries (get-in ext ["ext" "entries"])
                                :params (get ext "xs") :result-type (get ext "type")
                                ;; Ask the actual Java preparer about each original
                                ;; extern. No second, drifting whitelist here.
                                :preparation-error (failure #(j/invoke-static (:prepare basis) [[row]]))})))
        manifest (first (filter #(= "manifest" (get % "kind")) rows))]
    {:scope :static-ir-inventory-not-source-compatibility
     :roots (vec roots) :producer-version (get manifest "leanVersion")
     :declarations (count selected) :missing-static-dependencies missing
     :dynamic-application-sites (reduce + 0 (map #(get-in calls [% :dynamic-sites] 0) required))
     :initialization-plan (get manifest "initializationPlan")
     :row-runtime-links (vec (for [row selected
                                  :let [initializer (get-in row ["runtime" "initializer"])
                                        redirect (get-in row ["redirect" "name"])]
                                  :when (or initializer redirect)]
                              {:name (ir/name-label (get row "name"))
                               :initializer (when initializer (ir/name-label initializer))
                               :redirect (when redirect (ir/name-label redirect))}))
     :externs externs
     :unsupported-extern-count (count (filter :preparation-error externs))
     :closure-preparation-error (if (seq missing) "Missing static declarations"
                                   (failure #(j/invoke-static (:prepare basis) [(vec selected)])))
     :limits ["Preparation does not execute or establish value parity."
              "Dynamic closure targets and host-provided implementations need separate validation."
              "The module initialization plan is reported, not executed or accepted."
              "Java preparation does not implement or validate row initializer/redirect semantics."
              "No hosted parsing, elaboration, kernel admission or project loading occurs."]}))

(defn audit-entry [basis entry & [producer]]
  (let [artifacts (keep identity [(get-in entry [:source :fixture]) (:ir entry)])
        checked (mapv (fn [{:keys [path sha256]}]
                        (let [actual (lean-compatibility-corpus/sha256 path)]
                          (when (not= actual sha256)
                            (throw (ex-info "Corpus artifact hash mismatch"
                                            {:path path :expected sha256 :actual actual})))
                          {:path path :sha256 actual})) artifacts)]
    (merge (select-keys entry [:id :source :roots :pending :recorded-evidence :evidence])
           {:checked-artifacts checked
            :inventory
            (when-let [path (get-in entry [:ir :path])]
              (let [rows (j/rows path)
                    manifests (filter #(= "manifest" (get % "kind")) rows)]
                (when (not= 1 (count manifests))
                  (throw (ex-info "Corpus IR requires exactly one manifest" {:path path})))
                (when (and (:version producer)
                           (not= (:version producer) (get (first manifests) "leanVersion")))
                  (throw (ex-info "Corpus producer version mismatch" {:path path})))
                (inventory basis rows (:roots entry))))})))

(defn audit [basis manifest-path]
  (let [manifest (edn/read-string (slurp manifest-path))]
    (when (not= 1 (:schema manifest))
      (throw (ex-info "Unsupported compatibility corpus schema" {})))
    {:schema 1 :scope :research-compatibility-corpus :producer (:producer manifest)
     :producer-revision-verification :capture-provenance-and-artifact-hashes-not-encoded-in-ir
     :release-requires (:release-requires manifest)
     :entries (mapv #(audit-entry basis % (:producer manifest)) (:entries manifest))}))
