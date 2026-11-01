;; Run on the isolated enabled consumer basis: jars only, no project source.
(require '[clojure.java.io :as io]
         '[prototype.native-call :as native]
         '[prototype.mutable :as u]
         '[prototype.machine :as m])
(doseq [path ["prototype/native_call.clj" "prototype/native_nat.clj" "prototype/mutable.clj"]]
  (assert (= "jar" (.getProtocol (io/resource path))) (str "Non-jar runtime source: " path)))
(assert (nil? (find-ns 'pattern.llvm)))
(doseq [[symbol result] [["lean_nat_add" 42] ["lean_nat_sub" 0] ["lean_nat_mod" 20]
                        ["lean_nat_dec_eq" 0] ["lean_nat_dec_lt" 1]]]
  (let [functions {:entry {:params [0 1]
                           :body [:call 2 [:direct :native] [[:var 0] [:var 1]] [:return [:var 2]]]}
                   :native {:params [1 2] :runtime-extern symbol
                            :body [:let 3 [:runtime symbol [[:var 1] [:var 2]]] [:return [:var 3]]]}}
        program (native/open-program functions)
        initial (m/start (m/world functions) :entry [20 22])
        counts (volatile! {})
        actual (u/freeze (native/run! program (u/thaw initial) 20 true counts))]
    (assert (= 1 (:fused @counts)))
    (assert (= result (:result actual)))
    (assert (= (m/run initial) actual))
    (doseq [fuel (range 6)]
      (assert (= (m/run initial fuel) (u/freeze (native/run! program (u/thaw initial) fuel)))))))
(println :native-call-jar-smoke-passed {:operations 5 :fuel-prefixes 30 :program-specific-codegen false})
