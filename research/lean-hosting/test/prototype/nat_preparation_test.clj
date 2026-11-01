(ns prototype.nat-preparation-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io] [clojure.data.json :as json]
            [prototype.typed-blocks :as blocks] [prototype.typed-blocks-test :as fixture]
            [prototype.import-ir :as ir] [prototype.runtime-abi :as abi]
            [prototype.machine :as m] [prototype.mutable :as u]
            [prototype.native-heap :as native-heap] [prototype.lazy-runtime :as lazy]))

(def fixture-dir
  (first (filter #(.exists (io/file % "globals.jsonl"))
                 [(io/file "fixtures") (io/file "research/lean-hosting/fixtures")
                  (io/file (.getParentFile (.getParentFile (.getParentFile (.getAbsoluteFile (io/file *file*))))) "fixtures")])))
(defn actual-rows [file wanted]
  (with-open [input (io/reader (io/file fixture-dir file))]
    (reduce (fn [out line]
              (let [r (json/read-str line :key-fn keyword)]
                (if (contains? wanted (:name r)) (assoc out (:name r) r) out))) {} (line-seq input))))
(defn name-of [& parts] (reduce (fn [n p] ["str" n p]) ["anonymous"] parts))
(defn prepared [rows root]
  (blocks/prepare-unit (fixture/selected rows) [(fixture/name-of root)] fixture/profile {} fixture/budgets))
(defn literal [id type value body] ["vdecl" {:idx id} type {:lit {:v {:num {:v value}}}} body])
(defn rc-row [persistent]
  (fixture/row "rc" [(fixture/p 0 "tobject")] "tobject"
               ["inc" {:idx 0} 2 true persistent ["dec" {:idx 0} 2 false persistent (fixture/ret 0)]]))

(declare rc-world)

(deftest actual-nat-literal-call-and-borrowed-abi-facts
  (let [caller (name-of "GlobalProbe" "noncapturing") callee (name-of "Nat" "add")
        rows (actual-rows "globals.jsonl" #{caller callee}) r (get rows callee)
        params (mapv (fn [{:keys [x ty borrow]}] {:id (:idx x) :type ty :borrow borrow}) (get-in r [:ir :extern :xs]))
        signature {:params params :result-type (get-in r [:ir :extern :type]) :generation "actual-fixture/1" :extern "lean_nat_add"}
        fs (fixture/selected [(get rows caller)])
        result (blocks/prepare-unit fs [caller] fixture/profile {callee signature} fixture/budgets)
        f (get-in result [:unit :functions caller])]
    (is (= :ready (:status result)))
    (is (= [true true] (mapv :borrow (get-in result [:unit :intrinsics callee :params]))))
    (is (= "tagged" (get-in f [:blocks 0 :ops 0 :type])))
    (is (= 1 (get-in f [:blocks 0 :ops 0 :value])))
    (is (= (get-in fs [caller :body]) (blocks/legacy-body f)))
    (let [runtime-functions (into {} (map abi/lower) (vals rows))
          rebuilt (assoc-in runtime-functions [caller :body] (blocks/legacy-body f))]
      (doseq [kind [:owned :imported]]
        (let [[world value] (rc-world runtime-functions kind) initial (m/start world caller [value])
              terminal (m/run initial)]
          (is (= 184467440737095516161N (:result terminal)))
          (is (= (m/node initial value) (m/node terminal value)))
          (is (= (:heap initial) (:heap terminal)))
          (is (= 0 (get-in terminal [:stats :allocations])))
          (binding [fixture/*jvm-program* (lazy/open-program rebuilt)]
            (doseq [fuel (range 6) backend [:reference :mutable :jvm]]
              (is (= (m/run initial fuel)
                     (fixture/backend-run backend rebuilt
                                          (m/start (assoc world :functions rebuilt) caller [value]) fuel)))))))))
  (let [caller (name-of "GlobalProbe" "readValues") callee (name-of "GlobalProbe" "values")
        rows (actual-rows "globals.jsonl" #{caller callee})
        signature {:params [] :result-type (get-in rows [callee :ir :fdecl :type])
                   :generation "actual-declaration-boundary/1" :extern "GlobalProbe.values"}
        fs (fixture/selected [(get rows caller)])
        result (blocks/prepare-unit fs [caller] fixture/profile {callee signature} fixture/budgets)
        f (get-in result [:unit :functions caller])]
    ;; This is a known declaration signature boundary, not a native extern or
    ;; execution authorization. The real producer RC annotation is retained.
    (is (= :ready (:status result)))
    (is (= {:pc 1 :op :inc :id 2 :type "tobject" :count 1 :check true :persistent true}
           (get-in f [:blocks 1 :ops 0])))
    (is (= (get-in fs [caller :body]) (blocks/legacy-body f)))))

(deftest object-family-literals-preserve-type-value-and-carrier
  (doseq [type ["object" "tagged" "tobject"] value [7 (bigint 7) (biginteger 7) 184467440737095516160N]]
    (let [r (fixture/row "literal" [] type (literal 0 type value (fixture/ret 0)))
          fs (fixture/selected [r]) result (prepared [r] "literal")
          f (get-in result [:unit :functions (fixture/name-of "literal")]) body (blocks/legacy-body f)]
      (is (= :ready (:status result)))
      (is (= type (get-in f [:blocks 0 :ops 0 :type])))
      (is (identical? value (get-in f [:blocks 0 :ops 0 :value])))
      (is (= (get-in fs [(fixture/name-of "literal") :body]) body))
      (is (= (class value) (class (get-in body [2 1]))))))
  (let [r (fixture/row "literal" [] "void" (literal 0 "void" 0 (fixture/ret 0)))]
    (is (= :unsupported-literal (:reason (prepared [r] "literal"))))))

(deftest exact-rc-fields-scope-transfer-and-malformed-facts
  (doseq [persistent [false true]]
    (let [r (rc-row persistent) fs (fixture/selected [r]) name (fixture/name-of "rc")
          result (prepared [r] "rc") f (get-in result [:unit :functions name])
          root (get-in fs [name :typed-ir :root])]
      (is (= :ready (:status result)))
      (is (= (get-in fs [name :body]) (blocks/legacy-body f)))
      (is (= (if persistent 5 4) (count (blocks/legacy-body f))))
      (doseq [[index op check] [[0 :inc true] [1 :dec false]]]
        (is (= {:pc index :op op :id 0 :type "tobject" :count 2 :check check :persistent persistent}
               (get-in f [:blocks index :ops 0])))
        (is (= {0 "tobject"} (get-in f [:blocks index :scope])))
        (is (= {:kind :identity-registers} (get-in f [:blocks index :terminator :args]))))
      (doseq [[path value] [[[:body 1] [:var 99]] [[:body 2] -1]]]
        (is (fixture/invalid? #(fixture/prepare (assoc-in fs (into [name] path) value) ["rc"]))))
      (doseq [[field value] [[:count 3] [:check nil] [:persistent (not persistent)] [:id 99]]]
        (is (fixture/invalid? #(fixture/prepare (assoc-in fs [name :typed-ir :nodes root field] value) ["rc"]))))))
  (let [fs (fixture/selected [(rc-row false)]) name (fixture/name-of "rc") root (get-in fs [name :typed-ir :root])
        unknown (-> fs (assoc-in [name :body 1] [:var 99]) (assoc-in [name :typed-ir :nodes root :id] 99))]
    (is (fixture/invalid? #(fixture/prepare unknown ["rc"])))
    (is (fixture/invalid? #(fixture/prepare (update-in fs [name :body] conj false) ["rc"])))))

(deftest representation-compatibility-is-directional-at-each-transfer
  (doseq [[actual expected] (concat (for [a ["object" "tagged" "tobject"] e ["object" "tagged" "tobject"]] [a e])
                                    [["void" "tobject"] ["uint64" "tobject"]])
          transfer [:return :call :tail :jump]]
    (let [callee (fixture/row "callee" [(fixture/p 0 expected)] expected (fixture/ret 0))
          application {:fap {:c (fixture/name-of "callee") :ys [(fixture/arg 0)]}}
          body (case transfer
                 :return (fixture/ret 0)
                 :call ["vdecl" {:idx 1} expected application (fixture/ret 0)]
                 :tail ["vdecl" {:idx 1} expected application (fixture/ret 1)]
                 :jump ["jdecl" {:idx 2} [(fixture/p 1 expected)] (fixture/ret 1)
                        ["jmp" {:idx 2} [(fixture/arg 0)]]])
          caller (fixture/row "caller" [(fixture/p 0 actual)] (if (= transfer :call) actual expected) body)
          ready? (or (= actual expected) (and (= expected "tobject") (contains? #{"object" "tagged"} actual)))
          result (prepared [callee caller] "caller")]
      (is (= (if ready? :ready :fallback) (:status result)))
      (when-not ready? (is (= :type-compatibility (:reason result)))))))

(defn rc-world [fs kind]
  (let [w (m/world fs) node {:kind :mpz :tag 250 :fields [] :rc (if (= :owned kind) 1 0)
                           :integer 184467440737095516160N}]
    (case kind
      :scalar [w 7]
      (:owned :persistent) [(assoc w :heap {0 node} :next-id 1) (m/->Ref 0)]
      :imported [(assoc w :native-imports [(reify native-heap/NativeSource
                                           (contains-id? [_ id] (= 0 id))
                                           (lookup-node [_ id] (when (= 0 id) node)))]) (m/->Ref 0)])))

(deftest canonical-rc-roundtrip-all-prefixes-and-persistent-failures
  (doseq [persistent [false true] kind [:scalar :owned :persistent :imported]]
    (let [r (rc-row persistent) fs (fixture/selected [r]) name (fixture/name-of "rc")
          unit (:unit (prepared [r] "rc")) rebuilt (assoc-in fs [name :body] (blocks/legacy-body (get-in unit [:functions name])))
          [world value] (rc-world fs kind) initial (m/start world name [value])
          ;; Enter reconstructed code, rather than keeping the old PC while
          ;; replacing only the function table. Unknown PC copies intentionally
          ;; use ordinary interpretation in the lazy runtime.
          rebuilt-initial (m/start (assoc world :functions rebuilt) name [value])]
      (if (and persistent (= :owned kind))
        ;; Error states compare the same backend before/after reconstruction;
        ;; this preparation change does not repair legacy compiler error charging.
        (doseq [backend [:mutable :jvm]]
          (let [attempt (fn [functions start]
                          (let [machine (u/thaw start)]
                            (try (if (= backend :mutable) (u/run! machine 10)
                                     (lazy/run! (lazy/open-program functions) machine 10))
                                 (catch Throwable t [(class t) (.getMessage t) (ex-data t) (u/freeze machine)]))))]
            (is (= (attempt fs initial) (attempt rebuilt rebuilt-initial)))))
        (binding [fixture/*jvm-program* (lazy/open-program rebuilt)]
          (doseq [fuel (range 5) backend [:reference :mutable :jvm]]
            (let [expected (m/run initial fuel)
                  actual (fixture/backend-run backend rebuilt rebuilt-initial fuel)]
              (is (= expected actual))
              (when (= :paused (:status actual))
                (is (= (m/run initial) (fixture/backend-run backend rebuilt (m/resume actual nil) 10)))))))))))

(deftest rc-and-object-preparation-retains-resource-limits
  (let [fs (fixture/selected [(rc-row false)]) root [(fixture/name-of "rc")]]
    (doseq [key [:max-instructions :max-blocks :max-work]]
      (is (= :fallback (:status (blocks/prepare-unit fs root fixture/profile {} (assoc fixture/budgets key 1))))))))
