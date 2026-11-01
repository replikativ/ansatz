(ns java-ir-expr-loose-control-checks
 "Scratch/resource models and lowering ownership boundaries."
 (:require [clojure.test :refer [deftest is run-tests]]
  [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
  [java-ir-expr-loose-checks :as loose] [java-ir-expr-machinery-checks :as expr]
  [java-ir-expr-instantiate-checks :as pure] [java-ir-sync-task-checks :as sync]
  [java-ir-host-checks :as h] [java-ir-generation-checks :as g]
  [java-ir-continuation-checks :as k] [java-ir-logical-sharing-checks :as sharing]))
(def ^:dynamic *basis* nil)
(defn context [options] (binding [loose/*basis* *basis*] (loose/context options)))
(defn query-context [] (binding [loose/*basis* *basis*] (loose/query-context)))
(defn search-object [ctx e]
 (let [cls (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$LooseBVarSearch" true (:loader ctx))
       ctor (.getDeclaredConstructor cls (into-array Class [(:class ctx)]))]
  (.setAccessible ctor true) (.newInstance ctor (object-array [e]))))
(defn search! [search input i]
 (let [method (.getDeclaredMethod (class search) "apply" (into-array Class [Object Object]))]
  (.setAccessible method true) (.invoke method search (object-array [input i]))))

(deftest shared-composite-at-different-offsets-cannot-use-an-identity-only-visited-bit
 (let [{:keys [ctx]} (query-context) e (j/machine ctx)
       shared (loose/app! ctx e (loose/bvar! ctx e 1) (loose/sort! ctx e))
       input (loose/app! ctx e (loose/lam! ctx e (do (j/retain! ctx e shared) shared)) shared)]
  ;; Query1 first prunes shared at offset1, then must revisit it at offset0.
  (is (= 1 (loose/has? ctx e input 1))) (is (= 1 (loose/has? ctx e input 0)))
  (is (= 0 (loose/has? ctx e input 2))) (loose/cleanup! ctx e input)))

(deftest logical-mt-rc1-does-not-use-native-likely-shared-query-cache
 (let [{:keys [ctx]} (query-context) e (j/machine ctx)
       input (loose/app! ctx e (loose/bvar! ctx e 1) (loose/sort! ctx e))]
  (sharing/mark! ctx e input)
  (let [search (search-object ctx e) before (k/counters ctx e)]
   (is (false? (search! search input 0))) (is (= 1 (c/rc ctx input)))
   (is (sharing/mt? ctx input)) (is (empty? (h/private-value search "visited")))
   (is (= before (k/counters ctx e))))
  (loose/cleanup! ctx e input)))

(deftest atomic-query-work-interruption-and-cycle-models-leave-guest-owners-unchanged
 (doseq [interrupt? [false true]]
  (let [{:keys [ctx]} (query-context) e (j/machine ctx) input (loose/bvar! ctx e 1)
        search (search-object ctx e) before (k/counters ctx e)]
   ;; MODEL injects only the private invocation-local work scalar.
   (sync/private-set! search "work" (long (if interrupt? 1023 1000000)))
   (try
    (when interrupt? (.interrupt (Thread/currentThread)))
    (is (g/bad? #(search! search input 0)))
    (finally (when interrupt? (Thread/interrupted))))
   (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx input)))
   (loose/cleanup! ctx e input)))
 (let [{:keys [ctx]} (query-context) e (j/machine ctx)
       input (loose/app! ctx e (loose/bvar! ctx e 1) (loose/sort! ctx e))
       fields ^objects (.get ^java.lang.reflect.Field (:fields ctx) input) old (aget fields 0)]
  ;; MODEL replace one owning edge with a retained self-edge, then break it after
  ;; the atomic host-only failure. No failed guest invocation is unwound here.
  (j/retain! ctx e input) (aset fields 0 input) (j/release! ctx e old)
  (let [search (search-object ctx e) before (k/counters ctx e)]
   (is (re-find #"Cyclic Expr loose search" (c/failure #(search! search input 0))))
   (is (= before (k/counters ctx e))) (is (= 2 (c/rc ctx input))))
  (aset fields 0 (long 0)) (j/release! ctx e input) (loose/cleanup! ctx e input)))

(deftest lowering-all-composites-recomputes-original-cache-and-preserves-flags
 (doseq [role [3 4 5 6 7 8]]
  (let [{:keys [ctx] :as lab} (context {}) e (loose/machine lab)
        name (j/call ctx e "Lean.Name.str._override" [0 "binder"])
        make (fn [index]
          (case role
           3 (loose/app! ctx e (loose/bvar! ctx e index) (loose/sort! ctx e))
           (4 5) (j/call ctx e (str "model-setup-" (expr/roles role)) [name (loose/sort! ctx e) (loose/bvar! ctx e index) 3])
           6 (j/call ctx e (str "model-setup-" (expr/roles role)) [name (loose/sort! ctx e) (loose/bvar! ctx e index) (loose/bvar! ctx e index) 1])
           7 (j/call ctx e (str "model-setup-" (expr/roles role)) [0 (loose/bvar! ctx e index)])
           8 (j/call ctx e (str "model-setup-" (expr/roles role)) [name 2 (loose/bvar! ctx e index)])))
        _ (when (contains? #{4 5 6 8} role) (j/retain! ctx e name))
        input (make 5) expected (make 3) out (loose/lower! ctx e input 3 2)]
   (is (= (expr/scalar-bytes ctx expected) (expr/scalar-bytes ctx out)))
   (is (true? (h/private-value input "dead")))
   (when (contains? #{4 5 6 8} role) (is (identical? name (first (expr/fields ctx out)))))
   (when (contains? #{3 7} role) (sync/release! ctx e name))
   (sync/release! ctx e expected) (sync/release! ctx e out) (sync/close! ctx e))))

(deftest lowering-host-constructor-pause-forks-and-preserves-receiver-packets
 ;; MODEL observational Host prefix around the original BVar constructor body.
 (let [target (expr/roles 0) original (get-in (first (filter #(= target (get % "label")) (expr/records))) ["row" "ir" "fdecl" "body"])
       event (h/spec "loose_constructor_event" ["tobject"] [true] "object")
       body (c/let-ir 100 "object" (c/fap "loose-constructor-event" [(c/v 1)]) original)
       {:keys [ctx] :as lab} (context {:rows [(h/ext "loose-constructor-event" event)] :host-specs [event] :replacements {target body}})
       parent (loose/machine lab) input (loose/bvar! ctx parent 5)]
  (j/start! ctx parent "Lean.Expr.lowerLooseBVars._boxed" [input 3 2])
  (let [request (h/request! ctx parent) {child :engine} (j/fork! ctx parent [])]
   (is (= "loose_constructor_event" (.symbol request)))
   (doseq [e [parent child]]
    (let [packet (h/private-value (pure/state e) "call")]
     (is (true? (h/private-value packet "entered"))) (is (= [false] (vec (h/private-value packet "owned")))))
    (j/resume-host! ctx e (j/host-request ctx e) 0)
    (let [out (sync/finish! ctx e)]
     (is (= [3] (expr/fields ctx out))) (sync/release! ctx e out) (sync/close! ctx e))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-loose-control-checks)))
