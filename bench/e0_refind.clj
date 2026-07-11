;; E0 — calibration: re-find deleted Mathlib proofs.
;;
;; Sample N theorems from the mathlib store, strip their proofs, and try to
;; re-prove each statement with the relational pipeline (recall → best-first →
;; instance synthesis → kernel certify), EXCLUDING the theorem itself from
;; recall. The Lean-side counterpart (bench/e0_lean.clj generates it) runs
;; `aesop` / `exact?` on the same statements for the baseline comparison.
;;
;;   clj -J-Xmx12g -M -i bench/e0_refind.clj
;;
;; Writes bench/results/e0-ansatz.ndjson (one record per theorem) and prints a
;; summary. Failures are the PORT LIST: classify each into missing-tactic vs
;; missing-recall before reading too much into the solve rate.
(require '[ansatz.core :as a]
         '[ansatz.rel :as r]
         '[ansatz.recall :as recall]
         '[ansatz.export.storage :as storage]
         '[ansatz.store :as store]
         '[ansatz.kernel.expr :as e]
         '[ansatz.kernel.env :as env]
         '[clojure.java.io :as io]
         '[clojure.data.json :as json])
(import '[ansatz.kernel ConstantInfo])

(def N 50)
(def SEED 42)
(def MAX-TYPE-SIZE 250)
(def DEPTH 4)
(def MAX-NODES 2000)
(def RECALL-LIMIT 10)     ; tight specificity prefix; applyo confirms lazily in search
(def TIMEOUT-MS 30000)

(when-not (deref a/ansatz-env) (a/init! "mathlib"))
(def env0 (deref a/ansatz-env))

(def ctx (storage/prepare-verify (storage/open-store (store/resolve-existing "mathlib")) "mathlib"))
(def order (vec (:decl-order ctx)))
(def resolve-fn (:resolve-fn ctx))

;; ---- sample: seeded shuffle, resolve lazily until N qualify ----
(defn theorem? [^ConstantInfo ci] (= (.tag ci) ConstantInfo/THM))
(def sample
  (let [rng (java.util.Random. SEED)
        idxs (let [a (int-array (range (count order)))]
               (dotimes [i (count order)]
                 (let [j (.nextInt rng (count order)) t (aget a i)]
                   (aset a i (aget a j)) (aset a j t)))
               a)]
    (loop [i 0, acc []]
      (if (or (= (count acc) N) (>= i (count order)))
        acc
        (let [nm (nth order (aget idxs i))
              ci (when (recall/useful? nm) (try (resolve-fn nm) (catch Throwable _ nil)))]
          (if (and ci (theorem? ci) (<= (e/size (.type ^ConstantInfo ci)) MAX-TYPE-SIZE))
            (recur (inc i) (conj acc [nm ci]))
            (recur (inc i) acc)))))))
(println "sampled" (count sample) "theorems")
(io/make-parents "bench/results/x")
(spit "bench/results/e0-sample.edn" (pr-str (mapv first sample)))

;; ---- LAZY, tight recall provider (no eager confirm — applyo confirms during
;;      search), memoized per goal-type, self-excluded. See rel/recall-provider. ----
(defn provider-for [self-name deadline]
  (let [base (r/recall-provider env0 {:limit RECALL-LIMIT :exclude #{self-name}})
        memo (atom {})]
    (fn [s g]
      (when (> (System/nanoTime) @deadline)
        (throw (ex-info "deadline" {::deadline true})))
      (let [k (e/->string (r/zonk s (#'r/mvar-type s g)))]
        (or (@memo k)
            (let [cands (base s g)]
              (swap! memo assoc k cands)
              cands))))))

(defn refind [nm ^ConstantInfo ci]
  (let [ty (.type ci)
        [lctx concl _] (#'r/open-telescope {} ty 90)
        s0 (r/state env0 :lctx lctx)
        s1 (first (r/run 1 s0 (r/fresh concl (fn [g] (fn [s] (r/unit (assoc s ::g g)))))))
        g (::g s1)
        t0 (System/nanoTime)
        ;; deadline throws in `moves` (Clojure-side abort between kernel calls);
        ;; a single runaway kernel call (deep defeq) is aborted by interrupting
        ;; the worker thread — the Java kernel now polls Thread.isInterrupted().
        deadline (atom (+ t0 (* TIMEOUT-MS 1000000)))
        provider (provider-for nm deadline)
        ;; move set = closing tactics (leaves) ∪ recalled-lemma application
        ;; (refiners). rfl is the first wired closer; simp/omega/intro follow.
        moves (fn [s g]
                {:leaves [[8 (r/assumptiono g)]
                          [7 (r/rflo g)]]
                 :refiners (vec (for [[w cn] (provider s g)]
                                  [w (fn [g k] (r/applyo g cn k))]))})
        n-cands (try (count (provider s1 g)) (catch Throwable _ nil))
        fut (future (try {:sol (first (r/bestfirst g moves DEPTH s1 :max-nodes MAX-NODES :limit 1))}
                         (catch Throwable t {:err t})))
        outcome (deref fut TIMEOUT-MS ::timeout)
        _ (when (= outcome ::timeout)
            (future-cancel fut))            ; interrupts the worker → kernel unwinds
        ms (quot (- (System/nanoTime) t0) 1000000)]
    (cond
      (= outcome ::timeout) {:name nm :status :timeout :ms ms :candidates n-cands}
      (:err outcome) {:name nm :status :error :ms ms :candidates n-cands
                      :error (str (type (:err outcome)) ": " (.getMessage ^Throwable (:err outcome)))}
      (nil? (:sol outcome)) {:name nm :status :exhausted :ms ms :candidates n-cands}
      :else (let [cert (r/certify (:sol outcome) g)]
              {:name nm :status (if (:ok? cert) :proved :cert-failed)
               :ms ms :candidates n-cands}))))

(defn run-e0! []
 (with-open [w (io/writer "bench/results/e0-ansatz.ndjson")]
  (doseq [[i [nm ci]] (map-indexed vector sample)]
    (let [res (try (refind nm ci)
                   (catch Throwable t {:name nm :status :error :error (str (type t) ": " (.getMessage t))}))]
      (println (format "[%2d/%d] %-60s %s %sms cands=%s" (inc i) (count sample) nm
                       (name (:status res)) (:ms res "-") (:candidates res "-")))
      (.write w (json/write-str res)) (.write w "\n") (.flush w))))
 (let [rs (map #(json/read-str % :key-fn keyword) (line-seq (io/reader "bench/results/e0-ansatz.ndjson")))
      by (frequencies (map :status rs))]
  (println "\n=== E0 ansatz summary ===")
  (println "total:" (count rs) "|" by)
  (println "median ms (proved):" (let [xs (sort (keep #(when (= "proved" (:status %)) (:ms %)) rs))]
                                   (when (seq xs) (nth xs (quot (count xs) 2)))))))
