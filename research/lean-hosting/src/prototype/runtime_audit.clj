(ns prototype.runtime-audit
  "Static closure inventory. Exporter dependency traversal is not a complete
  initialization or dynamically selected callback reachability analysis."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [prototype.import-ir :as ir]
            [prototype.interop :as interop]
            [prototype.compact-bench :as provenance]))

(defn- walk-body [body visit]
  (visit body)
  (let [[op a b c d e f] body]
    (case op
      "vdecl" (walk-body d visit)
      "jdecl" (do (walk-body c visit) (walk-body d visit))
      ("set" "uset") (walk-body d visit)
      ("setTag" "del") (walk-body (last body) visit)
      "sset" (walk-body f visit)
      ("inc" "dec") (walk-body e visit)
      "case" (doseq [alt d] (walk-body (last alt) visit))
      ("ret" "jmp" "unreachable") nil
      (throw (ex-info "Unknown producer instruction during audit" {:body body})))))

(defn audit [path]
  (let [catalogue (ir/index-bundles [path]) rows (vals (:declarations catalogue))
        instructions (atom {}) expressions (atom {}) types (atom {})
        persistent-rc (atom 0) scalar-layouts (atom 0)
        failures
        (keep (fn [row]
                (when-let [f (get-in row [:ir :fdecl])]
                  (doseq [t (cons (:type f) (map :ty (:xs f)))] (swap! types update t (fnil inc 0)))
                  (walk-body
                   (:body f)
                   (fn [[op _ ty expr :as body]]
                     (swap! instructions update op (fnil inc 0))
                     (when (and (contains? #{"inc" "dec"} op) (nth body 4)) (swap! persistent-rc inc))
                     (when (= "vdecl" op)
                       (swap! types update ty (fnil inc 0))
                       (swap! expressions update (name (ffirst expr)) (fnil inc 0))
                       (when-let [layout (get-in expr [:ctor :i])]
                         (when (pos? (+ (:usize layout) (:ssize layout))) (swap! scalar-layouts inc)))))))
                (try (ir/lower-declaration row) nil
                     (catch clojure.lang.ExceptionInfo e
                       {:name (ir/name-label (:name row)) :message (.getMessage e) :data (ex-data e)}))) rows)
        failures (vec failures)
        externs (->> rows (keep #(get-in % [:ir :extern]))
                     (map (fn [ext] {:name (ir/name-label (:f ext)) :symbol (interop/extern-symbol ext)
                                    :params (mapv #(select-keys % [:ty :borrow]) (:xs ext))
                                    :return-type (:type ext)})) (sort-by :name) vec)
        groups (group-by :message failures)]
    {:producer (select-keys (first (:manifests catalogue)) [:schema :leanVersion])
     :input-sha256 (provenance/sha256 path)
     :declarations (count rows) :functions (count (filter #(get-in % [:ir :fdecl]) rows))
     :extern-count (count externs) :extern-symbol-count (count (set (map :symbol externs)))
     :manifest-initializers
     (let [modules (mapcat :modules (:manifests catalogue))]
       {:modules (count modules) :builtin (reduce + (map #(count (:builtinInitializers %)) modules))
        :regular (reduce + (map #(count (:initializers %)) modules))
        :scope "All modules loaded by native exporter; not a minimal initializer dependency closure"})
     :admitted-by-current-importer (- (count rows) (count failures))
     :instructions @instructions :expressions @expressions :runtime-types @types
     :persistent-rc-operations @persistent-rc :scalar-constructor-layouts @scalar-layouts
     :first-failure-per-declaration
     (into (sorted-map) (map (fn [[message failures]]
                              [message {:declarations (count failures) :examples (vec (take 5 failures))}]) groups))
     :externs externs
     :unreachable-functions (->> rows (filter #(= ["unreachable"] (get-in % [:ir :fdecl :body])))
                                  (mapv #(ir/name-label (:name %))))
     :limitations ["Static direct-call and closure-construction closure only"
                   "Module initializers and dynamically registered parser callbacks are additional roots"
                   "First lowering failure per declaration is not the full list of required fixes"
                   "Successful lowering does not imply linked, initialized or semantically compatible execution"]}))

(defn -main [& [path]]
  (println (json/write-str (audit path)))
  (shutdown-agents))
