;; Rewrite a store's blobs in a different codec (ansatz.export.codec):
;;
;;   clj -J-Xmx4g -M scripts/convert_store.clj <src-store> <dst-store> [branch] [boring|fressian]
;;
;; Copies each konserve key's value to the destination store PRESERVING ADDRESSES, so PSS
;; roots, branch metadata and every internal reference stay valid and nothing is rebuilt or
;; re-sorted. Only the encoding changes: konserve decodes each blob by the serializer in its
;; own header and re-encodes with the destination's, so the copy is exact.
;;
;; It WALKS THE FOUR PSS TREES from the branch metadata rather than enumerating the store.
;; Two reasons: `konserve.core/keys` reads every blob's metadata and, on a store written by an
;; older konserve, takes the v1 migration path, which casts a sync FileChannel to
;; AsynchronousChannel and throws (fixed in konserve after 0.9.395, not in any release yet);
;; and a walk copies only LIVE nodes, dropping superseded ones instead of carrying them over.
;;
;; The sidecars (attrs/discr-keys/simp-keys/instances.tsv) and the catalogue are ordinary files
;; next to the store, not blobs — copy them alongside. The source store is only ever read.
(require '[ansatz.export.storage :as storage]
         '[konserve.core :as k]
         '[clojure.java.io :as io])
(import '[org.replikativ.persistent_sorted_set Branch])

(let [[src dst branch codec-arg] *command-line-args*
      branch (or branch "mathlib")
      codec (keyword (or codec-arg "boring"))]
  (when-not (and src dst)
    (println "usage: convert_store.clj <src> <dst> [branch] [boring|fressian]")
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
        meta (or (k/get src-store [:branches branch] nil {:sync? true})
                 (throw (ex-info "no such branch" {:branch branch :store src})))
        roots (keep meta [:names-root :levels-root :exprs-root :env-root])
        seen (java.util.HashSet.)
        copied (atom 0)]
    (println "Converting branch" branch "of" src "->" dst "as" codec)
    (println "  roots:" (vec roots))
    ;; 1. the branch's own metadata and its decl-order chunks
    (k/assoc dst-store [:branches branch] meta {:sync? true})
    (if-let [n (:decl-order-chunks meta)]
      (dotimes [i n]
        (k/assoc dst-store [:decl-order branch i]
                 (k/get src-store [:decl-order branch i] nil {:sync? true}) {:sync? true}))
      (k/assoc dst-store [:decl-order branch]
               (k/get src-store [:decl-order branch] nil {:sync? true}) {:sync? true}))
    ;; 2. every live node reachable from the roots (explicit stack: the trees are deep)
    (let [stack (java.util.ArrayDeque.)]
      (doseq [r roots] (.push stack r))
      (while (not (.isEmpty stack))
        (let [addr (.pop stack)]
          (when (.add seen addr)
            (let [node (k/get src-store addr nil {:sync? true})]
              (when (nil? node)
                (throw (ex-info "node missing from source store" {:address addr})))
              (k/assoc dst-store addr node {:sync? true})
              (when (instance? Branch node)
                (doseq [a (.addresses ^Branch node)]
                  (when (and a (not (.contains seen a))) (.push stack a))))
              (when (zero? (mod (swap! copied inc) 20000))
                (let [rt (Runtime/getRuntime)]
                  (println "  copied" @copied "nodes, queue" (.size stack)
                           "elapsed-s" (quot (- (System/nanoTime) t0) 1000000000)
                           "mem-MB" (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576))
                  (flush))))))))
    (storage/close-store in)
    (storage/close-store out)
    (println "DONE:" @copied "nodes in" (quot (- (System/nanoTime) t0) 1000000000) "s")
    (shutdown-agents)))
