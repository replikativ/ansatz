(ns matched-prelude.store-only
  "Store-only conversion of an already authenticated matched Prelude pair.
   No TypeChecker, Env hydration, derived indices or guest extension authority."
  (:require [ansatz.export.parser :as parser]
            [ansatz.export.storage :as storage]
            [ansatz.store :as store]
            [clojure.data.json :as json]
            [clojure.java.io :as io])
  (:import [ansatz.kernel Name ExprStore]
           [java.security MessageDigest]))

(defn- require! [test message data]
  (when-not test (throw (ex-info message data))))

(defn- sha256 [file]
  (let [hash (MessageDigest/getInstance "SHA-256")
        buffer (byte-array 65536)]
    (with-open [input (io/input-stream file)]
      (loop []
        (let [n (.read input buffer)]
          (when (pos? n) (.update hash buffer 0 n) (recur)))))
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest hash)))))

(defn- typed-name [^Name n]
  (case (int (.tag n))
    0 ["anonymous"]
    1 ["str" (typed-name (.prefix n)) (.str n)]
    2 ["num" (typed-name (.prefix n)) (Long/toUnsignedString (.num n))]))

(defn- read-json [file] (json/read-str (slurp file) :key-fn keyword))

(defn import!
  "Run inside the root-coordinated bounded JVM. Output directory must not exist.
   `pair-directory` must contain the reviewed native pair-audit.json; its digest
   is a producer trust basis, not kernel proof verification or guest admission."
  [pair-directory output-directory {:keys [pair-audit-sha256]}]
  (let [file #(io/file pair-directory %)
        audit-file (file "pair-audit.json")
        audit (read-json audit-file)
        correspondence (read-json (file "correspondence.json"))
        entries (:constants correspondence)
        expected (into {} (map (juxt :typedName identity)) entries)
        branch "prelude"
        output (io/file output-directory)]
    (require! (and (string? pair-audit-sha256)
                   (= pair-audit-sha256 (sha256 audit-file)))
              "caller-pinned pair audit digest required" {})
    (require! (= #{:module-data.jsonl :kernel.ndjson :correspondence.json
                    :transport-receipt.json :build-cohort.json :typed-scalars.json :module-file-cohort.json}
                  (set (keys (:files audit)))) "unexpected paired input file set" {})
    (require! (= "matched-prelude-pair-audit/1" (:schema audit)) "wrong audit schema" {})
    (require! (and (= 2314 (:declarations audit) (count entries) (count expected))
                   (:checkingShapesEqual audit) (:dependencyClosure audit) (:familyClosure audit)
                   (:typedNameCollisionFree audit) (:displayKeyCollisionFree audit)
                   (:fullBodies audit) (:quotInit audit)) "incomplete source audit" {})
    (require! (not (.exists output)) "store staging output already exists" {:output (str output)})
    (doseq [[name evidence] (:files audit)]
      (require! (= (:sha256 evidence) (sha256 (file (clojure.core/name name))))
                "paired input hash mismatch" {:file name}))
    ;; Validate exact Java typed-Name ingress before PSS name-cmp can collapse
    ;; display-key collisions. The streaming parser retains file-backed Expr IDs.
    (let [seen (atom #{})
          displays (atom #{})
          parsed (parser/parse-ndjson-file-streaming-raw
                  (str (file "kernel.ndjson")) nil
                  (fn [_ shell]
                    (let [^Name n (:name shell)
                          typed (typed-name n)
                          item (get expected typed)
                          display (.toString n)]
                      (require! item "unexpected Java typed Name" {:name display})
                      (require! (= display (:displayName item)) "Java/Lean display mismatch" {:name display})
                      (require! (and (not (contains? @seen typed)) (not (contains? @displays display)))
                                "duplicate Java name or display collision" {:name display})
                      (swap! seen conj typed)
                      (swap! displays conj display))
                    nil))]
      (try
        (require! (= (set (keys expected)) @seen) "Java parser source domain differs" {})
        (finally (.close ^ExprStore (get-in parsed [:parser-state :exprs])))))
    (.mkdirs output)
    (let [sm (storage/open-store (str output) {:sync-blob? false :write-format 2})]
      (try
        (let [roots (storage/import-ndjson-streaming! sm (str (file "kernel.ndjson")) branch
                      :verbose? false :log-file (str (io/file output "import.log")))
              _ (require! (every? #(and (contains? roots %) (some? (get roots %)))
                                  [:env-root :exprs-root :names-root :levels-root])
                          "writer did not return all actual captured roots" {:roots roots})
              _ (require! (and (= 2314 (:env-count roots)) (:quot-enabled roots))
                          "stored domain or quotient mismatch" {:roots roots})
              _ (doseq [[name evidence] (:files audit)]
                  (require! (= (:sha256 evidence) (sha256 (file (clojure.core/name name))))
                            "paired input changed during conversion" {:file name}))
              manifest {:store/format 2 :branch branch
                        :ansatz/version "dev"
                        :artifact/cohort (sha256 audit-file)
                        :provenance {:basis :trusted-artifact
                                     :lean/version "4.33.1"
                                     :lean/commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
                                     :producer/pair-audit-sha256 (sha256 audit-file)
                                     :producer/files (:files audit)
                                     :projection/body-policy :full
                                     :proof-replay false}
                        :store/capabilities #{:kernel-lookup :exact-definition-hints}
                        :captured-branch-roots (select-keys roots [:env-root :exprs-root :names-root :levels-root])
                        :artifacts {:declarations (:env-count roots) :expressions (:exprs-count roots)
                                    :names (:names-count roots) :levels (:levels-count roots)}
                        :quot-enabled (:quot-enabled roots)
                        :derived-indexes false
                        :guest-finalization-accepted false
                        :created (java.util.Date.)}]
          (storage/flush-writes! (:storage sm))
          ;; Manifest is the final publication operation. Failed stages have none.
          (store/write-manifest! (str output) manifest)
          manifest)
        (finally (storage/close-store sm))))))
