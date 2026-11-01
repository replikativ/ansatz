;; Optional end-to-end campaign check. Requires the pinned collected module store.
;; clojure -J-Xss32m -J-Xmx2g -M scripts/parser-conformance.clj
(require '[clojure.data.json :as json]
         '[clojure.edn :as edn]
         '[clojure.string :as str]
         '[prototype.bootstrap :as bootstrap]
         '[prototype.declaration-store :as store]
         '[prototype.interop :as interop])

(let [[index-path store-path] *command-line-args*
      catalogue (store/open-index (or store-path "target/parser-module-store")
                                  (edn/read-string (slurp (or index-path "target/parser-module-index.edn"))))
      checkpoint (atom nil)
      started (System/nanoTime)
      session (bootstrap/load-file! {:module "ParserOracle"
                                     :roots ["ParserOracle.observeFull"]
                                     :backend :mutable
                                     :initialize-imports true
                                     :import-catalogue catalogue
                                     :initialization-fuel 10000000
                                     :checkpoint checkpoint})
      _ (println {:loaded true :frontend (:frontend session)
                  :actions (count (get-in session [:module-initialization :actions]))
                  :initialization-ms (/ (- (System/nanoTime) started) 1e6)})
      expected (mapv #(json/read-str % :key-fn keyword)
                     (str/split-lines (slurp "fixtures/parser-header-full-oracle.jsonl")))
      results
      (mapv (fn [observation]
              (let [start (System/nanoTime)
                    result (interop/call-io (assoc session :fuel 5000000)
                                           "ParserOracle.observeFull" [(:input observation)]
                                           {:arguments [:string] :result :string})
                    actual (json/read-str (:value result) :key-fn keyword)
                    report {:input (:input observation) :matches (= observation actual)
                            :elapsed-ms (/ (- (System/nanoTime) start) 1e6)}]
                (when-not (:matches report)
                  (throw (ex-info "Parser observation differs from native Lean"
                                  (assoc report :expected observation :actual actual))))
                (println report)
                report)) expected)]
  (println {:cases (count results) :matching (count (filter :matches results))
            :frontend-hosted false :parser-hosted true})
  (shutdown-agents))
