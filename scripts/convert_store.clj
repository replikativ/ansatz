;; Rewrite a store's blobs in a different codec (ansatz.export.codec):
;;
;;   clj -J-Xmx3g -M scripts/convert_store.clj <src-store-path> <dst-store-path> [boring|fressian]
;;
;; A blob-by-blob copy that PRESERVES ADDRESSES — each konserve key keeps its value, so PSS
;; roots, branch metadata and every internal reference stay valid and nothing is rebuilt or
;; re-sorted. Only the encoding changes: konserve decodes each blob by the serializer in its
;; own header and re-encodes with the destination store's, so the copy is exact.
;;
;; The sidecars (attrs/discr-keys/simp-keys/instances.tsv) and the catalogue are NOT touched;
;; copy or rebuild them alongside. The source store is only ever read.
(require '[ansatz.export.storage :as storage]
         '[konserve.core :as k]
         '[clojure.java.io :as io])

(let [[src dst codec-arg] *command-line-args*
      codec (keyword (or codec-arg "boring"))]
  (when-not (and src dst)
    (println "usage: convert_store.clj <src> <dst> [boring|fressian]")
    (System/exit 2))
  (when (.exists (io/file dst))
    (println "destination exists, refusing:" dst)
    (System/exit 2))
  (.mkdirs (io/file dst))
  (let [t0 (System/nanoTime)
        in (storage/open-store src)
        out (storage/open-store dst {:codec codec})
        src-store (:store in)
        dst-store (:store out)
        ks (mapv :key (k/keys src-store {:sync? true}))
        n (count ks)]
    (println "Converting" n "blobs from" src "to" dst "as" codec "...")
    (doseq [[i key] (map-indexed vector ks)]
      (let [v (k/get src-store key nil {:sync? true})]
        (k/assoc dst-store key v {:sync? true}))
      (when (zero? (mod (inc i) 20000))
        (let [rt (Runtime/getRuntime)]
          (println " " (inc i) "/" n
                   "elapsed-s" (quot (- (System/nanoTime) t0) 1000000000)
                   "mem-MB" (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576))
          (flush))))
    (storage/close-store in)
    (storage/close-store out)
    (println "DONE:" n "blobs in" (quot (- (System/nanoTime) t0) 1000000000) "s")
    (shutdown-agents)))
