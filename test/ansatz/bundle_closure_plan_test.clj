(ns ansatz.bundle-closure-plan-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.bundle-closure-plan :as closure]))

(def digest-a (apply str (repeat 64 "a")))
(def digest-b (apply str (repeat 64 "b")))
(def caps {:items 100000 :scalar-bytes 1000000 :depth 32 :rounds 20
           :observations 100 :roots 1000 :reasons 1000 :edges 1000 :names 1000})
(defn descriptor [text] {:text text :name [["str" text]]})
(defn capture
  ([] (capture [{:kind "csimp" :name "f" :target "g" :witness "w"}]))
  ([attrs]
   {:capture-id digest-a :native-names (mapv descriptor ["f" "g" "w" "h" "q"])
    :original-roots {:init ["f"] :lex ["f"] :sizeof ["f"]}
    :companions {:attrs attrs :matchers [] :instances []}}))
(defn observation [request names]
  {:capture-id digest-a :roots (mapv :text (:roots request)) :names names :raw-sha256 digest-b})
(defn reply [result role-names]
  (into {} (for [request (:requests result)]
             [(:role request) (observation request (get role-names (:role request)))])))
(defn step [c result role-names limits]
  (closure/next-round c (:state result) (reply result role-names) limits))
(defn refused [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:reason (ex-data e)))))

(deftest initialization-requires-no-observations
  (let [c (capture) result (closure/next-round c nil {} caps)]
    (is (= [:init :lex :sizeof] (mapv :role (:requests result))))
    (is (= [0 0 0] (mapv :round (:requests result))))
    (is (= [{:origin :configured :original-index 0}] (get-in result [:requests 0 :roots 0 :provenance])))
    (is (= :initial-observations-forbidden (refused #(closure/next-round c nil {:init {}} caps))))))

(deftest union-coverage-does-not-cover-a-role
  (let [c (capture) initial (closure/next-round c nil {} caps)
        result (step c initial {:init ["f" "g" "w"] :lex ["f"] :sizeof ["f"]} caps)]
    (is (= [:lex :sizeof] (mapv :role (:requests result))))
    (is (= {:init [] :lex ["g" "w"] :sizeof ["g" "w"]} (:derived-roots result)))
    (is (= (:original-roots c) (:original-roots result)))
    (is (= ["g" "w"] (get-in result [:observed-kernel-closure :init :names])))
    (is (= :csimp-witness (get-in result [:requests 0 :roots 2 :provenance 0 :edge-kind])))))

(deftest newly-exported-kernel-dependency-selects-another-row
  (let [c (capture [{:kind "impl" :name "f" :target "g"}
                    {:kind "impl" :name "h" :target "q"}])
        initial (closure/next-round c nil {} caps)
        one (step c initial (zipmap [:init :lex :sizeof] (repeat ["f"])) caps)
        two (step c one (zipmap [:init :lex :sizeof] (repeat ["f" "g" "h"])) caps)
        done (step c two (zipmap [:init :lex :sizeof] (repeat ["f" "g" "h" "q"])) caps)]
    (is (= ["g" "q"] (get-in two [:derived-roots :lex])))
    (is (= ["h"] (get-in two [:observed-kernel-closure :lex :names])))
    (is (= :closure-planned (:status done)))
    (is (empty? (:requests done)))
    (is (= :none (:authority done)))
    (is (= :not-performed (:promotion done)))
    (is (= :terminal-state (refused #(closure/next-round c (:state done) {} caps))))))

(deftest duplicate-registrations-retain-original-and-selected-addresses
  (let [row {:kind "csimp" :name "f" :target "g" :witness "w"}
        c (capture [{:kind "unfold" :name "q"} row row])
        initial (closure/next-round c nil {} caps)
        result (step c initial (zipmap [:init :lex :sizeof] (repeat ["f"])) caps)
        request (first (:requests result))]
    (is (= ["f" "g" "w"] (mapv :text (:roots request))))
    (is (= [1 2] (mapv :global-row-index (get-in request [:roots 1 :provenance]))))
    (is (= [0 1] (mapv :selected-row-index (get-in request [:roots 1 :provenance]))))
    (is (= [1 2] (get-in result [:selection-provenance :init :attrs])))
    (is (= 12 (get-in result [:usage :reasons])))))

(deftest matcher-local-annotations-are-not-global-roots
  (let [c (assoc-in (capture []) [:companions :matchers]
                    [{:name "f" :numParams 0 :numDiscrs 1 :uElimPos nil
                      :discrs ["localBinder"] :overlaps [] :alts []}])
        initial (closure/next-round c nil {} caps)
        result (step c initial (zipmap [:init :lex :sizeof] (repeat ["f"])) caps)]
    (is (= :closure-planned (:status result)))
    (is (= {:init [] :lex [] :sizeof []} (:derived-roots result)))))

(deftest exact-typed-descriptors-do-not-use-display-reconstruction
  (let [row {:text "«x.y».7" :name [["str" "x.y"] ["num" "7"]]}
        c (-> (capture []) (assoc :native-names [row])
              (assoc :original-roots (zipmap [:init :lex :sizeof] (repeat [(:text row)]))))
        result (closure/next-round c nil {} caps)]
    (is (= (:name row) (get-in result [:requests 0 :roots 0 :name])))
    (is (= (:text row) (get-in result [:requests 0 :roots 0 :text])))))

(deftest malformed-and-ambiguous-native-descriptors-refuse
  (doseq [rows [[(descriptor "f") (descriptor "f")]
                [(descriptor "f") {:text "alias" :name [["str" "f"]]}]
                [{:text "f" :name [["num" "9223372036854775808"]]}]
                [{:text "f" :name [["num" "01"]]}]
                [{:text "--f" :name [["str" "f"]]}]
                [{:text "f\u0000" :name [["str" "f"]]}]]]
    (is (some? (refused #(closure/next-round (assoc (capture []) :native-names rows) nil {} caps))))))

(deftest absent-descriptors-refuse-even-for-unselected-global-rows
  (let [c (capture [{:kind "impl" :name "q" :target "absent"}])]
    (is (= :missing-native-descriptor (refused #(closure/next-round c nil {} caps)))))
  (is (= :missing-native-descriptor
         (refused #(closure/next-round (assoc-in (capture []) [:original-roots :lex] ["absent"]) nil {} caps)))))

(deftest missing-unsolicited-and-stale-observations-refuse
  (let [c (capture) initial (closure/next-round c nil {} caps)
        observations (reply initial (zipmap [:init :lex :sizeof] (repeat ["f"])))]
    (doseq [bad [(dissoc observations :lex)
                 (assoc observations :other {})
                 (assoc-in observations [:lex :roots] ["g"])
                 (assoc-in observations [:lex :capture-id] digest-b)
                 (assoc-in observations [:lex :raw-sha256] "not-a-digest")]]
      (is (some? (refused #(closure/next-round c (:state initial) bad caps)))))))

(deftest omitted-root-and-shrinking-kernel-closure-refuse
  (let [c (capture) initial (closure/next-round c nil {} caps)]
    (is (= :requested-root-omitted
           (refused #(step c initial (zipmap [:init :lex :sizeof] (repeat ["g"])) caps))))
    (let [one (step c initial (zipmap [:init :lex :sizeof] (repeat ["f" "h"])) caps)]
      (is (= :export-closure-shrank
             (refused #(step c one (zipmap [:init :lex :sizeof] (repeat ["f" "g" "w"])) caps)))))))

(deftest immutable-state-branches-have-per-lineage-budgets
  (let [c (capture) limits (assoc caps :observations 3)
        initial (closure/next-round c nil {} limits)
        one (step c initial (zipmap [:init :lex :sizeof] (repeat ["f"])) limits)
        branch (step c initial (zipmap [:init :lex :sizeof] (repeat ["f"])) limits)]
    (is (= (:usage one) (:usage branch)))
    (is (= (:requests one) (:requests branch)))
    (is (= :limit (refused #(step c one (zipmap [:init :lex :sizeof] (repeat ["f" "g" "w"])) limits))))))

(deftest finite-caps-are-enforced-across-initialization-and-rounds
  (let [c (capture)]
    (doseq [[key maximum] [[:items 1] [:scalar-bytes 1] [:depth 1] [:roots 2]]]
      (is (= :limit (refused #(closure/next-round c nil {} (assoc caps key maximum))))))
    (doseq [[key maximum] [[:rounds 1] [:observations 2] [:names 2] [:edges 2] [:reasons 1]]]
      (let [limits (assoc caps key maximum)]
        (is (= :limit (refused #(let [initial (closure/next-round c nil {} limits)]
                                  (step c initial (zipmap [:init :lex :sizeof] (repeat ["f"])) limits))))))))
  (is (= :explicit-finite-limits-required
         (refused #(closure/next-round (capture) nil {} (assoc caps :rounds 0))))))

(deftest standard-container-and-scalar-preflight
  (let [trap (reify Object (hashCode [_] (throw (AssertionError. "must not hash"))))]
    (is (= :unsupported-data
           (refused #(closure/next-round (assoc (capture) :native-names [trap]) nil {} caps)))))
  (let [c (assoc (capture) :native-names (subvec (:native-names (capture)) 0 3))]
    (is (= :unsupported-data (refused #(closure/next-round c nil {} caps)))))
  (is (= :duplicate-name
         (refused #(closure/next-round (assoc-in (capture) [:original-roots :init] ["f" "f"]) nil {} caps)))))

(deftest lineage-inputs-cannot-be-replaced
  (let [c (capture) initial (closure/next-round c nil {} caps)]
    (is (= :different-lineage-inputs
           (refused #(closure/next-round (with-meta c {:copy true}) (:state initial) {} caps))))
    (is (= :different-lineage-inputs
           (refused #(closure/next-round c (:state initial) {} (with-meta caps {:copy true})))))))
