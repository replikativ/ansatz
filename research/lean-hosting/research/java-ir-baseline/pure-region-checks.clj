(ns java-ir-pure-region-checks
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-pure-region :as region]
            [prototype.import-ir :as ir]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]))

(def ^:dynamic *basis* nil)
(defn- raw [rows] (json/read-str (json/write-str rows)))
(defn- setup [rows label params result]
  (let [functions (into {} (map ir/lower-declaration rows))
        target (c/name-ir label)]
    {:functions functions :world (m/world functions)
     :plan (region/prepare *basis* (raw rows)
                           {:functions functions :target target :params params :result result})}))
(defn- identity-row [borrow]
  (c/decl "identity" [(assoc (c/p 1 "object") :borrow borrow)] "object"
          (if borrow ["inc" {:idx 1} 1 true false (c/ret 1)] (c/ret 1))))
(defn- failure [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e e)))
(defn- leaf [world kind value]
  (let [[world r] (m/allocate world kind (if (= kind :mpz) 250 249) [])]
    [(assoc-in world [:heap (:id r) (if (= kind :mpz) :integer :text)] value) r]))

(deftest pure-region-roundtrips-and-canonical-controls
  (doseq [[descriptor value] [[:nat 0] [:nat 184467440737095516160000N]
                             [:string "Aé€😀\n\u0000"]]]
    (let [{:keys [plan world]} (setup [(identity-row false)] "identity" [{:codec descriptor :borrow false}] descriptor)
          result (plan world [value])]
      (is (= value (:result result)))
      (is (= :done (:status result)))
      (is (nil? (:body result)))
      (is (= {} (:locals result) (:joins result)))
      (is (= [] (:frames result)))
      (is (= (:stats world) (:stats result)))
      (is (= value (:result (plan world [value])))))))

(deftest legacy-leaf-ownership-and-borrowed-decode
  (doseq [[descriptor kind value] [[:nat :mpz 999999999999999999999N] [:string :string "hello😀"]]
          borrow [true false]]
    (let [{:keys [plan world]} (setup [(identity-row borrow)] "identity" [{:codec descriptor :borrow borrow}] descriptor)
          [entry r] (leaf world kind value)
          result (plan entry [r])]
      (is (= value (:result result)))
      (is (= (if borrow 1 nil) (get-in result [:heap (:id r) :rc])))
      (is (= 1 (get-in entry [:heap (:id r) :rc]))))))

(deftest static-call-and-shared-argument-occurrences
  (let [rows [(identity-row false)
              (c/decl "first" [(c/p 1 "object") (c/p 2 "object")] "object"
                      ["dec" {:idx 2} 1 true false
                       (c/let-ir 3 "object" (c/fap "identity" [(c/v 1)]) (c/ret 3))])]
        {:keys [plan world]} (setup rows "first" [{:codec :string :borrow false} {:codec :string :borrow false}] :string)
        [entry r] (leaf world :string "shared")
        entry (m/retain entry r 1)
        result (plan entry [r r])]
    (is (= "shared" (:result result)))
    (is (empty? (:heap result)))
    (let [bad (failure #(plan (m/release entry r 1) [r r]))]
      (is (false? (:entered? (ex-data bad))))
      (is (= [0 1] (:remaining-argument-indices (ex-data bad)))))))

(deftest preflight-rejects-active-control-wrong-codecs-and-identity
  (let [{:keys [plan world]} (setup [(identity-row false)] "identity" [{:codec :nat :borrow false}] :nat)]
    (doseq [entry [(assoc world :status :running)
                   (assoc world :functions (into {} (:functions world)))]]
      (let [bad (failure #(plan entry [1]))]
        (is (false? (:entered? (ex-data bad))))
        (is (identical? entry (:checkpoint (ex-data bad))))))
    (is (false? (:entered? (ex-data (failure #(plan world ["wrong"]))))))))

(deftest malformed-preflight-never-creates-an-engine
  (let [{:keys [plan world]} (setup [(identity-row false)] "identity" [{:codec :string :borrow false}] :string)
        [entry r] (leaf world :string "retained")
        creates (atom 0)]
    (with-redefs [j/machine (fn [_] (swap! creates inc) (throw (ex-info "must not enter" {})))]
      (doseq [[packet args] [[entry []] [entry [r r]]
                             [(assoc entry :host-request {:dest 1}) [r]]
                             [(assoc entry :resume-var 1) [r]]
                             [(assoc entry :frames [{}]) [r]]
                             [entry [(m/->Ref 99999)]]
                             [(assoc-in entry [:heap (:id r) :rc] -1) [r]]
                             [entry [(String. (char-array [(char 0xd800)]))]]]]
        (let [bad (failure #(plan packet args))]
          (is (false? (:entered? (ex-data bad))))
          (is (identical? packet (:checkpoint (ex-data bad))))
          (is (= [0] (:remaining-argument-indices (ex-data bad)))))))
    (is (zero? @creates))
    (is (= 1 (get-in entry [:heap (:id r) :rc])))))

(deftest borrowed-aliases-share-one-external-owner
  (doseq [first-borrow [true false]]
    (let [rows [(c/decl "borrow-second"
                       [(assoc (c/p 1 "object") :borrow first-borrow)
                        (assoc (c/p 2 "object") :borrow true)] "object"
                       ["inc" {:idx 2} 1 true false
                        (if first-borrow (c/ret 2) ["dec" {:idx 1} 1 true false (c/ret 2)])])]
          {:keys [plan world]} (setup rows "borrow-second"
                                     [{:codec :string :borrow first-borrow} {:codec :string :borrow true}] :string)
          [entry r] (leaf world :string "borrowed-alias")
          entry (if first-borrow entry (m/retain entry r 1))
          result (plan entry [r r])]
      (is (= "borrowed-alias" (:result result)))
      (is (= 1 (get-in result [:heap (:id r) :rc])))
      (when-not first-borrow
        (let [bad (failure #(plan (m/release entry r 1) [r r]))]
          (is (false? (:entered? (ex-data bad)))))))))

(deftest execution-and-encoding-failure-never-consume-legacy-owners
  (let [{:keys [plan world]} (setup [(c/decl "trap" [(c/p 1 "object")] "object" ["unreachable"])]
                                  "trap" [{:codec :string :borrow false}] :string)
        [entry r] (leaf world :string "held")
        bad (failure #(plan entry [r]))]
    (is (:entered? (ex-data bad)))
    (is (= :execute (:stage (ex-data bad))))
    (is (identical? entry (:checkpoint (ex-data bad))))
    (is (= [0] (:remaining-argument-indices (ex-data bad)))))
  (let [{:keys [plan world]} (setup [(identity-row false)] "identity" [{:codec :string :borrow false}] :nat)
        [entry r] (leaf world :string "wrong-result")
        bad (failure #(plan entry [r]))]
    (is (= :encode (:stage (ex-data bad))))
    (is (:entered? (ex-data bad)))
    (is (identical? entry (:checkpoint (ex-data bad))))
    (is (= [0] (:remaining-argument-indices (ex-data bad))))))

(deftest partial-release-failure-reports-latest-world
  (let [rows [(c/decl "first" [(c/p 1 "object") (c/p 2 "object")] "object"
                     ["dec" {:idx 2} 1 true false (c/ret 1)])]
        {:keys [plan world]} (setup rows "first" [{:codec :string :borrow false} {:codec :string :borrow false}] :string)
        [world a] (leaf world :string "a") [entry b] (leaf world :string "b")
        release m/release calls (atom 0)
        bad (with-redefs [m/release (fn [s v n] (if (= 2 (swap! calls inc))
                                                 (throw (ex-info "injected release failure" {}))
                                                 (release s v n false)))]
              (failure #(plan entry [a b])))
        packet (ex-data bad)]
    (is (= :release (:stage packet)))
    (is (= [1] (:remaining-argument-indices packet)))
    (is (= [a b] (:region-arguments packet)))
    (is (= "a" (:encoded-result packet)))
    (is (nil? (get-in (:checkpoint packet) [:heap (:id a)])))
    (is (= 1 (get-in (:checkpoint packet) [:heap (:id b) :rc])))))

(deftest plan-rejects-extern-dynamic-recursive-and-changed-legacy-code
  (let [identity (identity-row false) functions (into {} [(ir/lower-declaration identity)])
        spec {:functions functions :target (c/name-ir "identity")
              :params [{:codec :nat :borrow false}] :result :nat}]
    (doseq [body [(c/let-ir 2 "object" {:ap {:x {:idx 1} :ys [(c/v 1)]}} (c/ret 2))
                  (c/let-ir 2 "object" (c/fap "identity" [(c/v 1)]) (c/ret 2))
                  ["suspend" {:idx 2} (c/ret 1)]]]
      (is (thrown? clojure.lang.ExceptionInfo
                   (region/prepare *basis* (raw [(assoc-in identity [:ir :fdecl :body] body)]) spec))))
    (is (thrown? clojure.lang.ExceptionInfo
                 (region/prepare *basis* (raw [identity])
                                 (assoc spec :functions (assoc-in functions [(c/name-ir "identity") :body] [:unreachable])))))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'java-ir-pure-region-checks)))
