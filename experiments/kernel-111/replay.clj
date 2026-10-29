;; Run with -Dansatz.kernel.experiment.congruence=true to measure the candidate.
;; The input is the exact Foundation closure from issue #111; all admission is checked.
(require '[ansatz.export.replay :as replay])
(import '[java.security MessageDigest] '[java.io FileInputStream])

(defn sha256 [path]
  (let [digest (MessageDigest/getInstance "SHA-256")
        buffer (byte-array 65536)]
    (with-open [in (FileInputStream. path)]
      (loop []
        (let [n (.read in buffer)]
          (when (pos? n) (.update digest buffer 0 n) (recur)))))
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest)))))

(let [path (first *command-line-args*)
      expected "ac77f75929e109a35e72ebe90466a6012c4a7d47c8924a95d2a32edf3dea845b"
      reported #{"LO.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4"
                 "LO.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2"
                 "LO.FirstOrder.Arithmetic.Bootstrapping.Substs.construction._proof_10"
                 "LO.FirstOrder.Arithmetic.Bootstrapping.Substs.construction._proof_11"}
      observations (atom [])
      original replay/replay-one]
  (assert path "Pass the Foundation export path")
  (assert (= expected (sha256 path)) "This experiment requires the exact issue #111 input")
  (let [result
        (with-redefs-fn
          {#'replay/default-fuel 1000000
           #'replay/replay-one
           (fn
             ([environment ci] (replay/replay-one environment ci true))
             ([environment ci verify?]
              (assert verify? "Unchecked admission is forbidden in this experiment")
              (let [start (System/nanoTime)
                    result (original environment ci verify?)
                    name (str (.name ^ansatz.kernel.ConstantInfo ci))]
                (when (reported name)
                  (let [row {:name name :elapsed-ms (/ (- (System/nanoTime) start) 1e6)
                             :result (second result)}]
                    (swap! observations conj row)
                    (prn row)))
                result)))}
          #(replay/replay-file-streaming path))]
    (prn {:stats (:stats result) :errors (:error-names result) :reported @observations})
    (when (or (seq (:error-names result)) (not= 15340 (get-in result [:stats :ok])))
      (System/exit 1))))
