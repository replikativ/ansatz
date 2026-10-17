(ns prototype.typed-call-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.interop :as interop]
            [prototype.lazy-runtime :as lazy]
            [prototype.machine :as m]
            [prototype.scalar :as scalar]))

(defn- name-of [s] ["str" ["anonymous"] s])
(def string-id (name-of "stringIdentity"))
(def bytes-id (name-of "bytesIdentity"))
(def option-id (name-of "optionIdentity"))
(def scalar-id (name-of "scalarIdentity"))
(def io-string (name-of "ioString"))
(def io-wide (name-of "ioWide"))
(def io-error (name-of "ioError"))
(def io-environment (name-of "ioEnvironment"))
(def functions
  {string-id {:params [0] :body [:return [:var 0]]}
   bytes-id {:params [0] :body [:return [:var 0]]}
   option-id {:params [0] :body [:return [:var 0]]}
   scalar-id {:params [0] :body [:return [:var 0]]}
   io-string (with-meta {:params [0 1] :body [:let 2 [:ctor 0 [[:var 0]]] [:return [:var 2]]]}
               {:runtime-param-types ["object" "void"]})
   io-wide (with-meta {:params [0 1] :body [:let 2 [:box "uint64" [:var 0]]
                                         [:let 3 [:ctor 0 [[:var 2]]] [:return [:var 3]]]]}
             {:runtime-param-types ["uint64" "void"]})
   io-error {:params [0] :body [:let 1 [:ctor 1 [[:imm "failure"]]] [:return [:var 1]]]}
   io-environment {:params [0] :body [:let 1 [:runtime "lean_io_getenv" [[:imm "ANSATZ_TEST"] [:var 0]]]
                                     [:let 2 [:ctor 0 [[:var 1]]] [:return [:var 2]]]]}})
(defn- session [backend] (interop/open-functions functions {} backend (lazy/code-cache)))

(deftest explicit-typed-calls-cover-strings-bytes-options-and-raw-scalars
  (doseq [backend [:reference :mutable :jvm]
          [target descriptor value] [[string-id :string "héλ😀\u0000"]
                                     [bytes-id :bytes [0 128 255]]
                                     [option-id [:option :bytes] {:some [4 5]}]
                                     [option-id [:option :unit] {:some nil}]
                                     [option-id [:option :nat] nil]
                                     [scalar-id :nat 18446744073709551616N]
                                     [scalar-id :bool true]
                                     [scalar-id :unit nil]
                                     [scalar-id :uint8 255]
                                     [scalar-id :uint16 65535]
                                     [scalar-id :uint32 4294967295]
                                     [scalar-id :uint64 18446744073709551615N]
                                     [scalar-id :usize 18446744073709551615N]
                                     [scalar-id :float -0.0]
                                     [scalar-id :float32 -0.0]]]
    (let [session (session backend)
          before (m/world functions)
          result (interop/call (assoc session :initial-world before) target [value]
                               {:arguments [descriptor] :result descriptor})]
      (if (#{:float :float32} descriptor)
        (is (= (scalar/float-bytes (name descriptor) value)
               (scalar/float-bytes (name descriptor) (:value result))))
        (is (= value (:value result))))
      (is (empty? (:heap before)))
      (when (m/ref? (get-in result [:state :result]))
        (is (empty? (:heap (m/release (:state result) (get-in result [:state :result]) 1))))))))

(deftest explicit-io-calls-append-world-and-decode-boxed-results
  (doseq [backend [:reference :mutable :jvm]]
    (let [session (session backend)
          string (interop/call-io session io-string ["hello λ"] {:arguments [:string] :result :string})
          wide (interop/call-io session io-wide [18446744073709551615N] {:arguments [:uint64] :result :uint64})]
      (is (= "hello λ" (:value string)))
      (is (= 18446744073709551615N (:value wide)))
      (is (= :done (get-in string [:state :status])))
      (is (= m/erased (get-in string [:state :locals 1])))
      (is (empty? (:heap (m/release (:state wide) (get-in wide [:state :result]) 1)))))))

(deftest typed-io-errors-carry-the-completed-world
  (doseq [backend [:reference :mutable :jvm]]
    (let [failure (try (interop/call-io (session backend) io-error [] {:arguments [] :result :nat})
                       (catch clojure.lang.ExceptionInfo e e))
          data (ex-data failure)]
      (is (= :guest-error (:type data)))
      (is (= "failure" (:guest-error data)))
      (is (= :done (get-in data [:state :status])))
      (is (= 1 (:tag (m/node (:state data) (get-in data [:state :result]))))))))

(deftest io-selection-validates-world-metadata-and-descriptor-counts
  (doseq [backend [:reference :mutable :jvm]]
    (let [session (session backend)
          invalid (assoc-in session [:functions io-string]
                            (with-meta (get functions io-string) {:runtime-param-types ["object" "object"]}))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"argument descriptor"
            (interop/call session string-id ["hello"] {:arguments [] :result :string})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Guest arity mismatch"
            (interop/call session string-id [] {:arguments [] :result :string})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"world token"
            (interop/call-io session string-id ["hello"] {:arguments [:string] :result :string})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"void world"
            (interop/call-io invalid io-string ["hello"] {:arguments [:string] :result :string})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small Nat"
            (interop/call session string-id ["legacy stays Nat"])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"small Nat"
            (interop/call session scalar-id [18446744073709551616N]))))))

(deftest typed-entry-calls-inherit-and-fork-the-completed-module-world
  (doseq [backend [:reference :mutable :jvm]]
    (let [world (assoc (m/world functions) :initialized-modules #{[:a :all]}
                       :environment {"ANSATZ_TEST" "captured"})
          session (assoc (session backend) :initial-world world)
          left (interop/call-io session io-environment [] {:arguments [] :result [:option :string]})
          right (interop/call-io session io-environment [] {:arguments [] :result [:option :string]})]
      (is (= {:some "captured"} (:value left)))
      (is (= left right))
      (is (= #{[:a :all]} (get-in left [:state :initialized-modules])))
      (is (empty? (get-in session [:initial-world :heap])))
      (is (= {"ANSATZ_TEST" "captured"} (get-in left [:state :environment]))))))
