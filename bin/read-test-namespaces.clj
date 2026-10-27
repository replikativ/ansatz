(ns ci.namespace-discovery
  "Read test declarations without evaluating them; reject ambiguous layouts."
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :as t])
  (:import [clojure.lang LineNumberingPushbackReader LispReader$ReaderException]
           [java.nio.file Files FileVisitOption]))

(defn fail! [file message]
  (throw (ex-info (str file ": " message)
                  {:kind :namespace-discovery-error :file (str file)})))

(defn read-form [file reader eof]
  (try
    (binding [*read-eval* false]
      (read {:eof eof} reader))
    (catch LispReader$ReaderException ex
      (fail! file (str "unsupported or malformed Clojure: " (.getMessage ex))))))

(defn namespace-change? [form]
  (cond
    (and (seq? form) (contains? '#{quote clojure.core/quote} (first form))) false
    (and (seq? form) (contains? '#{ns clojure.core/ns in-ns clojure.core/in-ns}
                               (first form))) true
    (coll? form) (boolean (some namespace-change? form))
    :else false))

(defn read-namespace [file]
  (with-open [reader (LineNumberingPushbackReader. (io/reader file))]
    (let [eof (Object.)
          form (read-form file reader eof)]
      (when-not (and (seq? form) (= 'ns (first form))
                     (symbol? (second form)) (nil? (namespace (second form))))
        (fail! file "expected a single ns declaration as the first form"))
      (let [tail (drop 2 form)
            tail (if (string? (first tail)) (rest tail) tail)
            tail (if (map? (first tail)) (rest tail) tail)]
        (when-not (every? #(and (seq? %) (contains? #{:refer-clojure :require :use :import :load :gen-class}
                                                   (first %))) tail)
          (fail! file "unsupported ns declaration clauses")))
      ;; Read the rest too: malformed files and additional declarations must not
      ;; become a successful discovery of only their first namespace.
      (loop []
        (let [next-form (read-form file reader eof)]
          (when-not (identical? next-form eof)
            (when (namespace-change? next-form)
              (fail! file "multiple or ambiguous namespace declarations"))
            (recur))))
      (str (second form)))))

(defn discover [root]
  (let [root (.normalize (.toAbsolutePath (.toPath (io/file root))))]
    (when-not (.isDirectory (.toFile root))
      (fail! root "test root is not a directory"))
    (with-open [stream (Files/walk root (make-array FileVisitOption 0))]
      (let [paths (vec (iterator-seq (.iterator stream)))
            _ (doseq [path paths]
                (when (Files/isSymbolicLink path)
                  (fail! path "symbolic links in a test root are unsupported")))
            entries (mapv (fn [path]
                            {:file (str path) :namespace (read-namespace (.toFile path))})
                          (sort-by str (filter #(and (.isFile (.toFile %))
                                                     (str/ends-with? (str %) "_test.clj")) paths)))]
        (doseq [[name entries] (group-by :namespace entries)]
          (when (> (count entries) 1)
            (fail! (:file (first entries))
                   (str "duplicate namespace " name " in " (mapv :file entries)))))
        (doseq [{:keys [file namespace]} entries]
          (let [expected (str (-> namespace (str/replace "." "/") (str/replace "-" "_")) ".clj")
                actual (str (.relativize root (.toPath (io/file file))))]
            (when-not (= expected actual)
              (fail! file (str "namespace " namespace " requires path " expected
                               ", found " actual)))))
        entries))))

(defn with-files [files f]
  (let [root (.toFile (Files/createTempDirectory "ansatz-discovery-" (make-array java.nio.file.attribute.FileAttribute 0)))]
    (try
      (doseq [[path content] files]
        (let [file (io/file root path)]
          (io/make-parents file)
          (spit file content)))
      (f root)
      (finally
        (doseq [file (reverse (file-seq root))] (.delete file))))))

(t/deftest reads-reader-supported-declarations
  (doseq [form ["(ns ^:no-doc sample.metadata-test)"
                "(ns ^{:doc \"metadata\"} sample.metadata-test \"docs\" {:author \"test\"})"]]
    (with-files {"sample/metadata_test.clj" (str ";; example: (ns misleading.comment-test)\n" form
                                                "\n(def example '(ns quoted.example-test))")}
      (fn [root]
        (t/is (= ["sample.metadata-test"] (mapv :namespace (discover root))))))))

(t/deftest rejects-unsupported-or-ambiguous-files
  (doseq [source ["" "(ns \"sample.metadata-test\")" "(do (ns sample.metadata-test))"
                  "(ns sample.metadata-test unexpected)"
                  "(ns sample.metadata-test) (ns sample.metadata-test)"
                  "(ns sample.metadata-test) (do (in-ns 'other))"
                  "(ns sample.metadata-test) (when true (ns hidden.other-test))"
                  "(ns sample.metadata-test) (" "(ns sample.metadata-test) #=(+ 1 2)"]]
    (with-files {"sample/metadata_test.clj" source}
      (fn [root]
        (t/is (thrown-with-msg? clojure.lang.ExceptionInfo #"metadata_test.clj"
                               (discover root)))))))

(t/deftest rejects-mismatched-paths-and-duplicate-namespaces
  (doseq [[files message]
          [[{"sample/wrong_test.clj" "(ns sample.actual-test)"}
            #"wrong_test.clj: namespace .* requires path"]
           [{"sample/duplicate_test.clj" "(ns sample.duplicate-test)"
             "other/duplicate_test.clj" "(ns sample.duplicate-test)"}
            #"duplicate namespace sample.duplicate-test"]]]
    (with-files files
      (fn [root]
        (t/is (thrown-with-msg? clojure.lang.ExceptionInfo message
                               (discover root)))))))

(t/deftest failing-fixture-is-selected-by-the-pinned-runner
  (let [root "bin/fixtures/namespace-discovery"
        names (mapv (comp symbol :namespace) (discover root))
        output (java.io.StringWriter.)
        result (binding [*out* output t/*test-out* output]
                 ((requiring-resolve 'cognitect.test-runner/test)
                  {:dir #{root} :namespace (set names)}))]
    (t/is (= ['ci.discovery-fixture-test] names))
    (t/is (= 1 (:test result)))
    (t/is (= 1 (:fail result)) "the intentional failure actually ran")
    (t/is (zero? (:error result)))
    (t/is (str/includes? (str output) "Testing ci.discovery-fixture-test"))))

(try
  (if (= ["--self-test"] (vec *command-line-args*))
    (let [result (t/run-tests 'ci.namespace-discovery)]
      (shutdown-agents)
      (System/exit (if (zero? (+ (:fail result) (:error result))) 0 1)))
    (do
      (when-not (= 1 (count *command-line-args*))
        (fail! "discovery" "expected one test root"))
      (println (json/write-str (discover (first *command-line-args*))))))
  (catch clojure.lang.ExceptionInfo ex
    (if (= :namespace-discovery-error (:kind (ex-data ex)))
      (do (binding [*out* *err*] (println (.getMessage ex))) (System/exit 1))
      (throw ex))))
