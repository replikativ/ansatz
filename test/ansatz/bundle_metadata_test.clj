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
                {:kind "unfold-thms" :name "recursive" :theorems ["recursive.eq_1" "recursive.eq_2"]}
                {:kind "class" :name "ExportedClass"}])
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

(def planner-v2 {:metadata-profile "ansatz-global-companions/2"})
(defn- corpora [attrs] {:attrs attrs :matchers [] :instances []})

(deftest planner-selection-keeps-missing-targets-without-weakening-strict-selection
  (let [rows [{:kind "csimp" :name "f" :target "g"}
              {:kind "impl" :name "inactive" :target "missing"}]]
    (is (= [(first rows)] (metadata/select-rows :attrs rows #{"f"})))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"missing declaration"
                          (metadata/select-for-names :attrs rows #{"f"})))
    (is (= [{:role :attrs :row-index 0 :source "f" :kind :csimp-target :target "g"}]
           (metadata/references :attrs [(first rows)])))
    (is (thrown? clojure.lang.ExceptionInfo
                 (metadata/select-rows :attrs (conj rows {:kind "unknown" :name "inactive"}) #{"f"}))))
  (testing "unselected malformed evidence also fails; selection is not a validation bypass"
    (is (thrown? clojure.lang.ExceptionInfo
                 (metadata/select-rows :attrs [{:kind "csimp" :name "inactive" :target "g"}]
                                       #{} planner-v2)))))

(deftest planner-references-preserve-types-order-and-explicit-witnesses
  (let [csimp {:kind "csimp" :name "f" :target "shared" :witness "f_eq_shared"}
        rows [csimp {:kind "impl" :name "g" :target "shared"}
              {:kind "unfold-thms" :name "h" :theorems ["h.eq_1" "shared"]}
              {:kind "simp" :name "ordinarySimp" :prio 1000}
              {:kind "unfold" :name "ordinaryUnfold"} {:kind "extern" :name "native"}]
        companions {:attrs rows :matchers [matcher] :instances [(first instance-rows)]}
        names #{"f" "g" "h" "ordinarySimp" "ordinaryUnfold" "native" "matcher" "first"}
        plan (metadata/plan-role :init companions names planner-v2)]
    (is (= rows (get-in plan [:rows :attrs])))
    (is (= [[:csimp-target "shared"] [:csimp-witness "f_eq_shared"]
            [:implementation-target "shared"] [:unfold-theorem "h.eq_1"]
            [:unfold-theorem "shared"] [:instance-class "Class"]]
           (mapv (juxt :kind :target) (:edges plan))))
    (is (= [0 0 1 2 2 0] (mapv :row-index (:edges plan))))
    (is (= [:attrs :attrs :attrs :attrs :attrs :instances] (mapv :role (:edges plan))))
    (is (= ["shared" "f_eq_shared" "h.eq_1" "Class"] (:missing-roots plan)))
    (is (= (:edges plan) (:missing-edges plan)))
    (is (= [] (metadata/references :matchers [matcher] planner-v2)))
    (testing "legacy parse/render/select remain strict and cannot silently lose witnesses"
      (is (thrown? clojure.lang.ExceptionInfo (metadata/render :attrs [csimp])))
      (is (thrown? clojure.lang.ExceptionInfo
                   (metadata/parse :attrs (json/write-str csimp))))
      (is (thrown? clojure.lang.ExceptionInfo
                   (metadata/select-for-names :attrs [csimp] #{"f" "shared" "f_eq_shared"}))))))

(deftest planner-keeps-each-kernel-role-independent
  (let [companions (corpora [{:kind "impl" :name "f" :target "runtimeTarget"}])
        init-plan (metadata/plan-role :init companions #{"f"})
        lex-plan (metadata/plan-role :lex companions #{"f" "runtimeTarget"})]
    (is (= ["runtimeTarget"] (:missing-roots init-plan)))
    (is (= [] (:missing-roots lex-plan)))
    (is (= [] (:missing-edges lex-plan)))
    (is (= :init (:kernel-role init-plan)))
    (is (= :lex (:kernel-role lex-plan)))
    (is (= (:edges init-plan) (:edges lex-plan))
        "a target present in another role does not satisfy the Init plan")))

(deftest planner-supports-explicit-fixed-point-inputs-without-assuming-export-success
  (let [companions (corpora [{:kind "csimp" :name "f" :target "g" :witness "f_eq_g"}
                             {:kind "impl" :name "g" :target "h"}
                             {:kind "unfold-thms" :name "h" :theorems ["h.eq_1"]}])
        plan #(metadata/plan-role :sizeof companions % planner-v2)
        initial (plan #{"f"})
        second-step (plan #{"f" "g" "f_eq_g"})
        third-step (plan #{"f" "g" "f_eq_g" "h"})
        fixed (plan #{"f" "g" "f_eq_g" "h" "h.eq_1"})]
    (is (= ["g" "f_eq_g"] (:missing-roots initial)))
    (is (= ["h"] (:missing-roots second-step)))
    (is (= ["h.eq_1"] (:missing-roots third-step)))
    (is (= [] (:missing-roots fixed)))
    (is (= [1 2 3 3] (mapv #(count (get-in % [:rows :attrs])) [initial second-step third-step fixed])))
    (is (= initial (plan #{"f"})) "a failed export never advances the planner's input")
    (is (= ["f_eq_g"] (:missing-roots (plan #{"f" "g" "h" "h.eq_1"})))
        "having all runtime targets does not discharge the witness edge")))

(deftest planner-rejects-ambiguous-options-and-malformed-witness-evidence
  (doseq [options [nil {:unknown true} {:metadata-profile "future"}]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (metadata/plan-role :init (corpora []) #{} options))))
  (doseq [row [{:kind "csimp" :name "f" :target "g"}
               {:kind "csimp" :name "f" :target "g" :witness ""}
               {:kind "csimp" :name "f" :target "g" :witness "eq" :unknown true}
               {:kind "impl" :name "f" :target "g" :witness "eq"}]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (metadata/references :attrs [row] planner-v2))))
  (is (thrown? clojure.lang.ExceptionInfo (metadata/plan-role :unknown (corpora []) #{})))
  (is (thrown? clojure.lang.ExceptionInfo (metadata/plan-role :init {:attrs []} #{})))
  (is (thrown? clojure.lang.ExceptionInfo (metadata/plan-role :init (corpora []) ["f"])))
  (is (thrown? clojure.lang.ExceptionInfo
               (metadata/references :attrs [{:kind "csimp" :name "f" :target "g" :witness "eq"}]))))
