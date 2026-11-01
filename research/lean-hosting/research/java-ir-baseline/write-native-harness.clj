(require '[clojure.java.io :as io] '[clojure.string :as str])
(let [[output] *command-line-args*
      _ (assert output "Pass the output Lean file")
      text (slurp "test/fixtures/unchanged-programs/rbmap.lean")
      needle "def main (xs"]
  (assert (and (<= 0 (.indexOf ^String text needle))
               (= (.indexOf ^String text needle) (.lastIndexOf ^String text needle))))
  (io/make-parents output)
  (spit output (str (str/replace text needle "def originalMain (xs")
                    (slurp "research/java-ir-baseline/native-harness-tail.lean"))))
