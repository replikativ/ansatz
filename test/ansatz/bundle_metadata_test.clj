(ns ansatz.bundle-metadata-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.data.json :as json]
            [ansatz.bundle-metadata :as metadata])
  (:import [java.io ByteArrayOutputStream]
           [java.nio.charset StandardCharsets]
           [java.util.zip GZIPOutputStream]))

(def attr-rows [{:kind "simp" :name "quoted.\"λ\\name" :prio 1000 :post false :inv true}
                {:kind "unfold" :name "definition"}
                {:kind "extern" :name "native"}
                {:kind "csimp" :name "original" :target "replacement"}
                {:kind "impl" :name "opaque" :target "implementation"}
                {:kind "unfold-thms" :name "recursive" :theorems ["recursive.eq_1" "recursive.eq_2"]}])
(def matcher {:name "matcher" :numParams 2 :numDiscrs 1 :uElimPos 3
              :discrs ["localBinder"] :overlaps [[0 1]]
              :alts [{:numFields 1 :numOverlaps 0 :unitThunk false}
                     {:numFields 0 :numOverlaps 1 :unitThunk false}]})
(def instance-rows [{:class "Class" :name "first" :priority 4294967295}
                    {:class "Class" :name "second" :priority 0}
                    {:class "Class" :name "third" :priority 1000}])
(defn- gzip [text]
  (let [out (ByteArrayOutputStream.)]
    (with-open [gz (GZIPOutputStream. out)] (.write gz (.getBytes ^String text StandardCharsets/UTF_8)))
    (.toByteArray out)))

(deftest strict-rows-roundtrip-with-order-and-escaped-names
  (doseq [[role rows] [[:attrs attr-rows] [:matchers [matcher]] [:instances instance-rows]]]
    (let [text (metadata/render role rows)]
      (is (= rows (metadata/parse role text)))
      (is (= text (metadata/render role (metadata/parse role text))))
      (is (= "\n" (subs text (dec (count text)))))))
  (is (= [] (metadata/parse :attrs "")))
  (is (= "" (metadata/render :instances []))))

(deftest malformed-attribute-rows-are-never-dropped-or-defaulted
  (doseq [row [{:kind "unknown" :name "x"}
               {:kind "simp" :name "x"}
               {:kind "simp" :name "x" :prio -1}
               {:kind "simp" :name "x" :prio 4294967296}
               {:kind "simp" :name "x" :prio 1.5}
               {:kind "simp" :name "x" :prio 1 :post false}
               {:kind "simp" :name "x" :prio 1 :post false :inv "false"}
               {:kind "csimp" :name "x"}
               {:kind "impl" :name "x" :target ""}
               {:kind "unfold" :name "x" :prio 1000}
               {:kind "extern" :name " "}
               {:kind "unfold-thms" :name "x" :theorems [nil]} [] nil]]
    (is (thrown? clojure.lang.ExceptionInfo (metadata/parse :attrs (json/write-str row)))))
  (doseq [text ["{" "{}\n\n" "\n" "{\"kind\":\"extern\",\"name\":\"x\"}\nmalformed"
                "{\"kind\":\"extern\",\"name\":\"x\"} trailing"
                "{\"kind\":\"extern\",\"name\":\"x\",\"name\":\"y\"}"]]
    (is (thrown? clojure.lang.ExceptionInfo (metadata/parse :attrs text)))))

(deftest matcher-shapes-and-reference-ranges-are-validated
  (doseq [row [(dissoc matcher :uElimPos)
               (assoc matcher :numParams -1)
               (assoc matcher :numDiscrs 2)
               (assoc matcher :uElimPos "0")
               (assoc matcher :discrs [false])
               (assoc matcher :overlaps [[0 2]])
               (assoc matcher :overlaps [[1 1]])
               (assoc matcher :overlaps [[0 1] [0 1]])
               (assoc-in matcher [:alts 0 :unitThunk] nil)
               (assoc-in matcher [:alts 0 :numFields] 0.5)
               (assoc matcher :unknown true)]]
    (is (thrown? clojure.lang.ExceptionInfo (metadata/parse :matchers (json/write-str row)))))
  (testing "universe elimination position is not a term-parameter index"
    (is (= [matcher] (metadata/parse :matchers (json/write-str matcher)))))
  (testing "empty alternatives describe empty elimination, not malformed metadata"
    (let [empty-matcher (assoc matcher :alts [] :overlaps [] :discrs [nil])]
      (is (= [empty-matcher] (metadata/parse :matchers (json/write-str empty-matcher)))))))

(deftest instance-tsv-needs-exactly-three-explicit-bounded-fields
  (doseq [text ["Class\tinstance" "Class\tinstance\t" "Class\tinstance\t-1"
                "Class\tinstance\t4294967296" "Class\tinstance\t1.0"
                "Class\tinstance\t1\textra" "\tinstance\t1000" "Class\t\t1000"]]
    (is (thrown? clojure.lang.ExceptionInfo (metadata/parse :instances text))))
  (is (= instance-rows (metadata/parse :instances (metadata/render :instances instance-rows)))))

(deftest selection-checks-global-references-but-not-local-discriminant-binders
  (is (= [matcher] (metadata/select-for-names :matchers [matcher] #{"matcher"})))
  (is (= [] (metadata/select-for-names :attrs [{:kind "impl" :name "absent" :target "alsoAbsent"}] #{})))
  (is (= [(nth attr-rows 3)]
         (metadata/select-for-names :attrs attr-rows #{"original" "replacement"})))
  (doseq [[role rows names] [[:attrs attr-rows #{"original"}]
                             [:attrs attr-rows #{"recursive" "recursive.eq_1"}]
                             [:instances instance-rows #{"first"}]]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"missing declaration"
                          (metadata/select-for-names role rows names))))
  (let [result (metadata/select-and-report :instances instance-rows #{"Class" "first" "third"})]
    (is (= [(first instance-rows) (last instance-rows)] (:rows result)))
    (is (= {:input 3 :selected 2 :excluded 1 :excluded-names ["second"]} (:report result)))))

(deftest compressed-resource-validation-is-shape-only-and-strict
  (let [resources {:attrs (gzip (metadata/render :attrs attr-rows))
                   :matchers (gzip (metadata/render :matchers [matcher]))
                   :instances (gzip (metadata/render :instances instance-rows))}]
    (is (= {:attrs attr-rows :matchers [matcher] :instances instance-rows}
           (metadata/validate-resources! resources)))
    (is (thrown? clojure.lang.ExceptionInfo (metadata/validate-resources! (dissoc resources :instances))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (metadata/validate-resources! (assoc resources :attrs (gzip "{}")))))))
