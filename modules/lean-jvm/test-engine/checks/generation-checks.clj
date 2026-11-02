(ns java-ir-generation-checks
  "Small executable-generation programs; no frontend or Init image."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-host-checks :as h]
            [java-ir-main-checks :as main]
            [java-ir-extern-checks :as x]))
(def ^:dynamic *basis* nil)
(defn prepare [rows] (j/prepare-host-program *basis* (x/raw rows) []))
(defn extend [ctx rows] (j/extend-program ctx (x/raw rows)))
(defn literal [label n]
  (c/decl label [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/lit n) (c/ret 2))))
(def common
  [(c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1))
   (c/decl "apply" [(c/p 1 "object") (c/p 2 "object")] "object"
           (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))])
(defn field [object name] (h/private-value object name))
(defn bad? [f] (not= "NO ERROR" (c/failure f)))
(defn count-functions [ctx] (.functionCount (:program ctx)))

(deftest ancestor-closures-and-constant-owners-survive-installation
  (doseq [explicit? [false true]
          :let [ctx (assoc (prepare (conj common (c/object-constant "constant"))) :explicit explicit?)
                next (extend ctx [(literal "answer" 42) (c/object-constant "new-constant")])
                engine (j/machine ctx) value (j/call ctx engine "constant" [])
                closure (j/make-closure! ctx engine "identity" [])
                old-id (j/function-id ctx "identity")]]
    (try
      (is (= old-id (j/function-id next "identity")))
      (is (= (+ 2 (count-functions ctx)) (count-functions next)))
      (j/install-program! next engine)
      (is (= 2 (c/rc ctx value)))
      (let [again (j/call next engine "constant" [])]
        (is (identical? value again)) (j/release! next engine again))
      (is (false? (aget ^booleans (field engine "constantReady") (j/function-id next "new-constant"))))
      (is (= 41 (j/call next engine "apply" [closure 41])))
      (is (= 42 (j/call next engine "answer" [0])))
      (let [fresh (j/call next engine "new-constant" [])]
        (is (not (identical? value fresh)))
        (is (true? (aget ^booleans (field engine "constantReady") (j/function-id next "new-constant"))))
        (j/release! next engine fresh))
      (j/release! next engine value)
      (is (= 1 (c/rc ctx value)))
      (finally (j/close! next engine)))))

(deftest siblings-have-independent-code-despite-equal-appended-ids
 (doseq [explicit? [false true]]
  (let [base (assoc (prepare common) :explicit explicit?)
        a (extend base [(literal "branch" 1)]) b (extend base [(literal "branch" 2)])
        parent (j/machine base) child (:engine (j/fork! base parent []))]
    (try
      (j/install-program! a parent) (j/install-program! b child)
      (is (= (j/function-id a "branch") (j/function-id b "branch")))
      (is (= 1 (j/call a parent "branch" [0])))
      (is (= 2 (j/call b child "branch" [0])))
      (doseq [label ["branch" "identity"]]
        (let [foreign (j/make-closure! b child label [])]
          (is (bad? #(j/call a parent "identity" [foreign])))
          (is (bad? #(j/call a parent "apply" [foreign 0])))
          (is (= "idle" (j/phase a parent)))
          (is (= 1 (c/rc b foreign)))
          (j/install-program! a parent)
          (j/release! b child foreign)))
      (let [own (j/make-closure! a parent "branch" [])]
        (is (= 1 (j/call a parent "apply" [own 0]))))
      (is (bad? #(j/function-id base "branch")))
      (finally (j/close! a parent) (j/close! b child))))))

(deftest pending-host-call-can-link-and-return-new-code-without-reentry
  (let [base (j/prepare-host-program *basis*
               (x/raw [(h/ext "resolve" h/owned)
                       (c/decl "over" [(c/p 1 "object")] "object"
                               (c/let-ir 2 "object" {:pap {:c (c/name-ir "resolve") :ys []}}
                                 (c/let-ir 3 "object" {:ap {:x {:idx 2} :ys ["erased" (c/v 1)]}} (c/ret 3))))]) [h/owned])
        a (extend base [(literal "linked" 10)]) b (extend base [(literal "linked" 20)])
        parent (j/machine base)]
    (j/start! base parent "over" [42])
    (let [request (h/request! base parent) child (:engine (j/fork! base parent []))
          child-request (j/host-request base child)]
      (try
        (j/install-program! a parent)
        (is (identical? request (j/host-request a parent)))
        (let [closure (j/make-closure! a parent "linked" [])]
          (is (bad? #(j/resume-host! base child child-request closure)))
          (is (identical? child-request (j/host-request base child)))
          (j/resume-host! a parent request closure)
          (is (= 10 (h/finish! a parent))))
        (j/install-program! b child)
        (j/resume-host! b child child-request (j/make-closure! b child "linked" []))
        (is (= 20 (h/finish! b child)))
        (finally (j/close! a parent) (j/close! b child))))))

(deftest generation-extends-host-registry-without-changing-inherited-abis
  (let [base (j/prepare-host-program *basis* (x/raw [(h/ext "old-host" h/owned)]) [h/owned])
        spec (assoc h/owned :parameters ["uint32"] :result "uint32")
        next (j/extend-program base (x/raw [(h/ext "new-host" spec)]) [spec])
        engine (j/machine base)]
    (try
      (j/install-program! next engine)
      (doseq [label ["old-host" "new-host"]]
        (j/start! next engine label [41])
        (let [request (j/host-request next engine)]
          (is (= "research_host" (j/request-value request "symbol")))
          (j/resume-host! next engine request 42)
          (is (= 42 (j/take-result! next engine)))))
      (is (bad? #(j/extend-program next [] [spec])))
      (is (bad? #(j/extend-program base [] [(assoc h/owned :symbol "lean_nat_add")])))
      (finally (j/close! next engine)))))

(deftest preparation-failure-never-mutates-the-base-program
  (let [base (prepare common) engine (j/machine base) size (count-functions base)]
    (try
      (doseq [rows [[(literal "identity" 0)]
                    [(literal "fresh" 0) (literal "fresh" 1)]
                    [(c/decl "missing" [(c/p 1 "object")] "object"
                             (c/let-ir 2 "object" (c/fap "unknown" [(c/v 1)]) (c/ret 2)))]]]
        (is (bad? #(extend base rows)))
        (is (= size (count-functions base)))
        (is (= 42 (j/call base engine "identity" [42]))))
      (is (identical? (:program base) (:program (extend base []))))
      (finally (j/close! base engine)))))

(deftest installation-rejects-running-complete-closed-and-failed-states
  (let [base (prepare common) next (extend base [(literal "new" 7)]) engine (j/machine base)]
    (j/start! base engine "identity" [42])
    (is (= "running" (j/phase base engine)))
    (is (bad? #(j/install-program! next engine)))
    (is (bad? #(j/make-closure! base engine "identity" [])))
    (is (j/advance! base engine 100))
    (is (= "complete" (j/phase base engine)))
    (is (bad? #(j/install-program! next engine)))
    (is (= 42 (j/take-result! base engine)))
    (j/install-program! next engine)
    (j/install-program! next engine)
    (j/close! next engine)
    (is (bad? #(j/install-program! next engine)))
    (is (bad? #(j/make-closure! next engine "identity" []))))
  (let [base (j/prepare-host-program *basis* (x/raw [(h/ext "host" h/owned)]) [h/owned])
        next (extend base [(literal "new" 7)]) engine (j/machine base)]
    (j/start! base engine "host" [0])
    (j/fail-host! base engine (j/host-request base engine) (ex-info "probe" {}))
    (is (bad? #(j/install-program! next engine)))
    (is (bad? #(j/make-closure! next engine "new" [])))
    (is (bad? #(j/close! base engine)))))

(deftest installation-rejects-rollback-sibling-and-unrelated-programs
  (let [base (prepare common) a (extend base [(literal "a" 1)]) b (extend base [(literal "b" 2)])
        other (prepare common) engine (j/machine base)]
    (try
      (j/install-program! a engine)
      (doseq [invalid [base b other]]
        (is (bad? #(j/install-program! invalid engine)))
        (is (= 1 (j/call a engine "a" [0]))))
      (finally (j/close! a engine)))))

(deftest mutable-input-name-lists-cannot-rewrite-future-linking
  (let [row (first (x/raw [(first common)])) name (java.util.ArrayList. ^java.util.Collection (get row "name"))
        base (j/prepare-host-program *basis* [(assoc row "name" name)] [])]
    (.set name 2 "caller-mutated")
    (let [next (extend base [(c/decl "call-old" [(c/p 1 "object")] "object"
                                    (c/let-ir 2 "object" (c/fap "identity" [(c/v 1)]) (c/ret 2)))])
          engine (j/machine base)]
      (try
        (j/install-program! next engine)
        (is (= 42 (j/call next engine "call-old" [42])))
        (is (bad? #(j/function-id base "caller-mutated")))
        (finally (j/close! next engine))))))

(deftest make-closure-preflights-captures-and-clones-their-array
  (let [base (prepare (conj common (h/fresh-object)
                           (c/decl "first" [(c/p 1 "object") (c/p 2 "object")] "object"
                                   ["dec" {:idx 2} 1 true false (c/ret 1)])
                           (c/object-constant "nullary")
                           (c/decl "scalar" [(c/p 1 "uint8")] "uint8" (c/ret 1))
                           ((x/originals) "Array.size") ((x/originals) "Array.getInternalBorrowed")))
        engine (j/machine base) value (j/call base engine "fresh" [0])]
    (try
      (doseq [operation [#(j/make-closure! base engine "identity" [value])
                         #(j/make-closure! base engine "scalar" [])
                         #(j/make-closure! base engine "nullary" [])
                         #(j/make-closure! base engine "Array.size" [])
                         #(j/make-closure! base engine "Array.getInternalBorrowed" [])
                         #(j/make-closure! base engine "first" [nil])]]
        (is (bad? operation))
        (is (= 1 (c/rc base value))))
      (let [array (object-array [value])
            method (.getMethod ^Class (:class base) "makeClosure"
                               (into-array Class [Integer/TYPE (class array)]))
            closure (.invoke method engine (object-array [(int (j/function-id base "first")) array]))]
        (aset array 0 0)
        (is (identical? value (aget ^objects (.get ^java.lang.reflect.Field (:fields base) closure) 0)))
        (is (identical? value (j/call base engine "apply" [closure 0])))
        (j/release! base engine value)
        (is (= 0 (c/rc base value))))
      (finally (j/close! base engine)))))

(deftest new-batch-resolves-forward-and-mutually-referenced-functions
  (let [base (prepare common)
        next (extend base
                     [(c/decl "a" [(c/p 1 "object")] "object"
                              (c/let-ir 2 "object" (c/fap "b" [(c/v 1)]) (c/ret 2)))
                      (c/decl "b" [(c/p 1 "object")] "object"
                              (c/let-ir 2 "object" {:pap {:c (c/name-ir "a") :ys []}}
                                ["dec" {:idx 2} 1 true false (c/ret 1)]))])
        engine (j/machine base)]
    (try
      (j/install-program! next engine)
      (is (= 42 (j/call next engine "a" [42])))
      (is (= 43 (j/call next engine "b" [43])))
      (finally (j/close! next engine)))))

(deftest deep-ancestry-tokens-do-not-retain-historical-program-tables
  (let [base (prepare common) engine (j/machine base)
        closure (j/make-closure! base engine "identity" [])
        next (reduce (fn [ctx n] (extend ctx [(literal (str "generation-" n) n)])) base (range 128))
        token (field closure "metadata") token-class (class token) program-class (class (:program base))]
    (try
      (is (not (.isInstance ^Class program-class token)))
      (doseq [f (.getDeclaredFields token-class)
              :when (not (java.lang.reflect.Modifier/isStatic (.getModifiers f)))
              :let [t (.getType f)]]
        (is (or (.isPrimitive t) (= token-class t)
                (and (.isArray t) (= token-class (.getComponentType t))))))
      (is (not-any? #(= program-class (.getType ^java.lang.reflect.Field %))
                    (.getDeclaredFields program-class)))
      (j/install-program! next engine)
      (is (= 42 (j/call next engine "apply" [closure 42])))
      (is (= 127 (j/call next engine "generation-127" [0])))
      (finally (j/close! next engine)))))

(deftest inherited-private-stream-closures-keep-owner-guards-and-fork-rebinding
  (let [base (assoc (binding [main/*basis* *basis*] (main/context)) :explicit true)
        next (extend base [(literal "new" 7)]) parent (j/machine base)
        partial (j/call base parent "partial-put" ["old"])]
    (j/install-program! next parent)
    (let [{:keys [engine roots]} (j/fork! next parent [partial]) child engine
          stranger (j/machine (assoc next :explicit false))]
      (try
        (is (bad? #(j/call next stranger "apply-zero" [partial])))
        (j/install-program! next stranger)
        (is (= "" (main/stdout next stranger)))
        (is (= 1 (c/rc next partial)))
        (doseq [[engine value] [[parent partial] [child (first roots)]]]
          (let [result (j/call next engine "apply-zero" [value])]
            (j/release! next engine result)
            (is (= "old" (main/stdout next engine)))))
        (finally (j/close! next parent) (j/close! next child) (j/close! next stranger))))))

(deftest repeated-captures-transfer-a-credit-per-occurrence
  (let [base (prepare [(h/fresh-object)
                       (c/decl "capture-three" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")]
                               "object" ["dec" {:idx 2} 1 true false
                                         ["dec" {:idx 3} 1 true false (c/ret 1)]])])
        engine (j/machine base) value (j/call base engine "fresh" [0])]
    (try
      (is (bad? #(j/make-closure! base engine "capture-three" [value value])))
      (is (= 1 (c/rc base value)))
      (j/retain! base engine value)
      (let [closure (j/make-closure! base engine "capture-three" [value value])
            fields (.get ^java.lang.reflect.Field (:fields base) closure)]
        (is (identical? (aget ^objects fields 0) (aget ^objects fields 1)))
        (is (= 2 (c/rc base value)))
        (j/release! base engine closure)
        (is (= 0 (c/rc base value))))
      (finally (j/close! base engine)))))

(deftest nested-mutable-prefix-name-keys-are-frozen
  (let [prefix (java.util.ArrayList. ^java.util.Collection (c/name-ir "prefix"))
        raw-name (java.util.ArrayList. ^java.util.Collection ["str" prefix "identity"])
        row (-> (first (x/raw [(first common)]))
                (assoc "name" raw-name)
                (assoc-in ["ir" "fdecl" "f"] ["str" (c/name-ir "prefix") "identity"]))
        base (j/prepare-host-program *basis* [row] [])]
    (.set prefix 2 "caller-mutated")
    (let [next (extend base
                       [(c/decl "call-old" [(c/p 1 "object")] "object"
                                (c/let-ir 2 "object" {:fap {:c ["str" (c/name-ir "prefix") "identity"]
                                                           :ys [(c/v 1)]}} (c/ret 2)))])
          engine (j/machine base)]
      (try
        (j/install-program! next engine)
        (is (= 42 (j/call next engine "call-old" [42])))
        (is (bad? #(j/function-id base "caller-mutated.identity")))
        (finally (j/close! next engine))))))

(deftest descriptor-only-extension-is-distinct-from-an-empty-no-op
  (let [base (prepare common) with-abi (j/extend-program base [] [h/owned])
        next (extend with-abi [(h/ext "host" h/owned)]) engine (j/machine base)]
    (try
      (is (not (identical? (:program base) (:program with-abi))))
      (is (= (count-functions base) (count-functions with-abi)))
      (is (identical? (:program with-abi) (:program (extend with-abi []))))
      (j/install-program! next engine)
      (j/start! next engine "host" [41])
      (j/resume-host! next engine (j/host-request next engine) 42)
      (is (= 42 (j/take-result! next engine)))
      (finally (j/close! next engine)))))

(deftest prepared-layouts-belong-to-program-slots-and-inherit-without-relinking
  (let [base (prepare common)
        a (extend base [(literal "branch" 10)])
        b (extend base [(c/decl "branch" [(c/p 7 "object")] "object"
                               (c/let-ir 100 "object" (c/lit 20) (c/ret 100)))])
        slots #(field (:program %) "preparedBodies")
        inherited (slots base) as (slots a) bs (slots b)
        id (j/function-id a "branch")]
    (doseq [i (range (count-functions base))]
      (is (identical? (aget inherited i) (aget as i)))
      (is (identical? (aget inherited i) (aget bs i))))
    (is (not (identical? (aget as id) (aget bs id))))
    (is (= 101 (field (aget bs id) "width")))
    (let [function (aget (field (:program base) "functions") 0)
          fields (.getDeclaredFields (class function))]
      (is (not-any? #{"body" "width" "joinWidth"} (map #(.getName %) fields)))
      (is (every? #(java.lang.reflect.Modifier/isFinal (.getModifiers %)) fields)))
    (doseq [explicit? [false true] [ctx answer] [[a 10] [b 20]]
            :let [ctx (assoc ctx :explicit explicit?) engine (j/machine ctx)]]
      (try (is (= answer (j/call ctx engine "branch" [0])))
           (finally (j/close! ctx engine))))))

(deftest active-and-saved-layouts-survive-host-install-and-fork
  (let [wrap #(h/wrap-static %1 %2 "object" identity)
        base (j/prepare-host-program *basis*
               (x/raw [(h/ext "host" h/owned) (wrap "inner" "host") (wrap "outer" "inner")])
               [h/owned])
        next (extend base [(literal "later" 99)])
        parent (j/machine base)]
    (j/start! base parent "outer" [41])
    (let [request (h/request! base parent)
          active (field parent "activePrepared")
          continuations (field parent "continuations")
          saved (mapv #(field % "callerPrepared")
                      (take (j/depth base parent) continuations))
          child (:engine (j/fork! base parent []))]
      (try
        (j/install-program! next parent)
        (is (identical? active (field parent "activePrepared")))
        (is (identical? active (field child "activePrepared")))
        (is (every? true? (map identical? saved
                           (map #(field % "callerPrepared")
                             (take (count saved) (field child "continuations"))))))
        (j/resume-host! next parent request 42)
        (j/resume-host! base child (j/host-request base child) 43)
        (is (= 42 (h/finish! next parent)))
        (is (= 43 (h/finish! base child)))
        (is (nil? (field parent "activePrepared")))
        (is (nil? (field child "activePrepared")))
        (finally (j/close! next parent) (j/close! base child))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-generation-checks)))
