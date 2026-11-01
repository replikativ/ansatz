(ns java-ir-host-checks
  "Small explicit host-request programs; no Init/frontend image or real IO."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-continuation-checks :as k]
            [java-ir-extern-checks :as x]))
(def ^:dynamic *basis* nil)
(defn spec [symbol parameters borrowed result]
  {:symbol symbol :parameters parameters :borrowed borrowed :result result})
(defn ext [label {:keys [symbol parameters borrowed result]}]
  {:kind "decl" :name (c/name-ir label)
   :ir {:extern {:f (c/name-ir label)
                 :xs (mapv (fn [i ty borrow] (assoc (c/p (inc i) ty) :borrow borrow))
                           (range) parameters borrowed)
                 :type result :ext {:entries [(x/extern-entry "c" symbol)]}}}})
(def owned (spec "research_host" ["object"] [false] "object"))
(def borrowed (spec "research_borrowed" ["object"] [true] "object"))
(def scalar (spec "research_scalar" ["object"] [false] "uint32"))
(defn prepare [rows descriptors]
  (j/prepare-host-program *basis* (x/raw rows) descriptors))
(defn args [request] (vec (j/request-value request "arguments")))
(defn request! [ctx engine]
  (loop [left 1000]
    (when (zero? left) (throw (ex-info "Host test did not suspend" {})))
    (if-let [request (j/host-request ctx engine)] request
      (do (assert (not (j/advance! ctx engine 1))) (recur (dec left))))))
(defn finish! [ctx engine] (k/finish! ctx engine [1 3 7]))
(defn wrap-static [label target result-type after]
  (c/decl label [(c/p 1 "object")] result-type
          (c/let-ir 2 result-type (c/fap target [(c/v 1)]) (after (c/ret 2)))))
(defn private-value [target label]
  (let [field (.getDeclaredField (class target) label)]
    (.setAccessible field true) (.get field target)))

(deftest static-call-forks-pending-request-and-completes-once-per-branch
  (let [ctx (prepare [(ext "host" owned) (wrap-static "caller" "host" "object" identity)] [owned])
        parent (j/machine ctx)]
    (j/start! ctx parent "caller" [41])
    (let [a (request! ctx parent)
          {:keys [engine]} (j/fork! ctx parent []) child engine b (j/host-request ctx child)
          before [(j/instructions ctx parent) (k/counters ctx parent)]]
      (try
        (is (= "host-call" (j/phase ctx parent) (j/phase ctx child)))
        (is (= "research_host" (j/request-value a "symbol")))
        (is (= ["object"] (vec (j/request-value a "paramTypes"))))
        (is (= [false] (vec (j/request-value a "borrowed"))))
        (is (= "object" (j/request-value a "resultType")))
        (is (= [41] (args a) (args b)))
        (is (not (identical? a b)))
        (is (false? (j/advance! ctx parent 100)))
        (is (= before [(j/instructions ctx parent) (k/counters ctx parent)]))
        (is (re-find #"(?i)request" (c/failure #(j/resume-host! ctx child a 99))))
        (is (identical? b (j/host-request ctx child)))
        (j/resume-host! ctx parent a 42)
        (j/resume-host! ctx child b 43)
        (is (= 42 (finish! ctx parent)))
        (is (= 43 (finish! ctx child)))
        (is (re-find #"(?i)request|host" (c/failure #(j/resume-host! ctx parent a 44))))
        (is (= "idle" (j/phase ctx parent)))
        (finally (j/close! ctx parent) (j/close! ctx child))))))

(deftest invalid-replies-preserve-the-pending-request
  (let [ctx (prepare [(ext "host" scalar) (wrap-static "caller" "host" "uint32" identity)] [scalar])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "caller" [0])
      (let [request (request! ctx engine)]
        (doseq [invalid [nil -1 4294967296 1.5 "bad" (Object.)]]
          (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine request invalid))))
          (is (identical? request (j/host-request ctx engine)))
          (is (= "host-call" (j/phase ctx engine))))
        (j/resume-host! ctx engine request 4294967295)
        (is (= 4294967295 (finish! ctx engine))))
      (finally (j/close! ctx engine)))))

(deftest request-accessors-do-not-expose-the-live-argument-or-abi-arrays
  (let [ctx (prepare [(ext "host" owned)] [owned]) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "host" [41])
      (let [request (j/host-request ctx engine)]
        (is (re-find #"ownership cleanup" (c/failure #(j/close! ctx engine))))
        (is (identical? request (j/host-request ctx engine)))
        (aset ^objects (j/request-value request "arguments") 0 99)
        (aset ^objects (j/request-value request "paramTypes") 0 "uint32")
        (aset-boolean ^booleans (j/request-value request "borrowed") 0 true)
        (is (= [41] (args request)))
        (is (= ["object"] (vec (j/request-value request "paramTypes"))))
        (is (= [false] (vec (j/request-value request "borrowed"))))
        (j/resume-host! ctx engine request 42)
        (is (= "complete" (j/phase ctx engine)))
        (is (= 42 (j/take-result! ctx engine))))
      (finally (j/close! ctx engine)))))

(deftest sequential-requests-do-not-accept-the-previous-completion
  (let [ctx (prepare [(ext "host" owned)
                      (c/decl "twice" [(c/p 1 "object")] "object"
                              (c/let-ir 2 "object" (c/fap "host" [(c/v 1)])
                                (c/let-ir 3 "object" (c/fap "host" [(c/v 2)]) (c/ret 3))))] [owned])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "twice" [41])
      (let [a (request! ctx engine)]
        (j/resume-host! ctx engine a 42)
        (let [b (request! ctx engine)]
          (is (= [42] (args b)))
          (is (not (identical? a b)))
          (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine a 99))))
          (is (identical? b (j/host-request ctx engine)))
          (j/resume-host! ctx engine b 43)
          (is (= 43 (finish! ctx engine)))))
      (finally (j/close! ctx engine)))))

(deftest static-borrow-does-not-release-a-caller-credit
  (let [ctx (prepare [(c/object-constant "child") (ext "host" borrowed)
                      (wrap-static "caller" "host" "object" #(vector "dec" {:idx 1} 1 true false %))] [borrowed])
        engine (j/machine ctx) child (j/call ctx engine "child" [])]
    (try
      (j/start! ctx engine "caller" [child])
      (let [request (request! ctx engine)]
        (is (= 2 (c/rc ctx child)))
        (j/resume-host! ctx engine request 7)
        (is (= 2 (c/rc ctx child)))
        (is (= 7 (finish! ctx engine)))
        (is (= 1 (c/rc ctx child))))
      (finally (j/close! ctx engine)))))

(deftest root-borrow-adapter-releases-only-its-own-credit
  (let [ctx (prepare [(c/object-constant "child") (ext "host" borrowed)] [borrowed])
        engine (j/machine ctx) child (j/call ctx engine "child" [])]
    (try
      (j/start! ctx engine "host" [child])
      (let [request (j/host-request ctx engine)]
        (is (identical? child (first (args request))))
        (is (= 2 (c/rc ctx child)))
        (j/retain! ctx engine child)
        (j/resume-host! ctx engine request child)
        (is (= 2 (c/rc ctx child)))
        (is (identical? child (j/take-result! ctx engine)))
        (j/release! ctx engine child)
        (is (= 1 (c/rc ctx child))))
      (finally (j/close! ctx engine)))))

(deftest owned-host-result-transfers-an-argument-without-double-release
  (let [ctx (prepare [(c/object-constant "child") (ext "host" owned)] [owned])
        engine (j/machine ctx) child (j/call ctx engine "child" [])]
    (try
      (j/start! ctx engine "host" [child])
      (j/resume-host! ctx engine (j/host-request ctx engine) child)
      (is (identical? child (j/take-result! ctx engine)))
      (is (= 2 (c/rc ctx child)))
      (j/release! ctx engine child)
      (is (= 1 (c/rc ctx child)))
      (finally (j/close! ctx engine)))))

(deftest pap-mixed-borrows-survive-a-pending-fork
  (let [mixed (spec "research_mixed" ["object" "object"] [true false] "object")
        ctx (prepare [(c/object-constant "a") (c/object-constant "b") (ext "host" mixed)
                      (c/decl "partial" [(c/p 1 "object")] "object"
                              (c/let-ir 2 "object" {:pap {:c (c/name-ir "host") :ys [(c/v 1)]}} (c/ret 2)))
                      (c/decl "apply" [(c/p 1 "object") (c/p 2 "object")] "object"
                              (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))] [mixed])
        parent (j/machine ctx) a (j/call ctx parent "a" []) b (j/call ctx parent "b" [])
        closure (j/call ctx parent "partial" [a])]
    (j/start! ctx parent "apply" [closure b])
    (let [request (request! ctx parent) child (:engine (j/fork! ctx parent []))
          branch-request (j/host-request ctx child) [ca cb] (args branch-request)]
      (try
        (is (= [a b] (args request)))
        (is (not (identical? a ca)))
        (is (= 2 (c/rc ctx a) (c/rc ctx ca)))
        (j/resume-host! ctx parent request b)
        (j/resume-host! ctx child branch-request cb)
        (is (= 1 (c/rc ctx a) (c/rc ctx ca)))
        (is (identical? b (finish! ctx parent)))
        (is (identical? cb (finish! ctx child)))
        (j/release! ctx parent b) (j/release! ctx child cb)
        (is (= 1 (c/rc ctx b) (c/rc ctx cb)))
        (finally (j/close! ctx parent) (j/close! ctx child))))))

(deftest overapplication-resumes-into-the-returned-guest-closure
  (let [ctx (prepare [(ext "host" owned)
                      (c/decl "id" [(c/p 1 "object")] "object" (c/ret 1))
                      (c/decl "id-closure" [] "object"
                              (c/let-ir 1 "object" {:pap {:c (c/name-ir "id") :ys []}} (c/ret 1)))
                      (c/decl "over" [(c/p 1 "object") (c/p 2 "object")] "object"
                              (c/let-ir 3 "object" {:pap {:c (c/name-ir "host") :ys []}}
                                (c/let-ir 4 "object" {:ap {:x {:idx 3} :ys [(c/v 1) (c/v 2)]}} (c/ret 4))))] [owned])
        engine (j/machine ctx) closure (j/call ctx engine "id-closure" [])]
    (try
      (j/start! ctx engine "over" [0 42])
      (let [request (request! ctx engine)]
        (is (= [0] (args request)))
        (j/resume-host! ctx engine request closure)
        (is (= 42 (finish! ctx engine))))
      (finally (j/close! ctx engine)))))

(deftest applied-scalar-result-is-boxed-for-the-object-application-abi
  (doseq [[descriptor reply expected] [[scalar 4294967295 4294967295]
                                      [(assoc scalar :result "usize")
                                       (biginteger "18446744073709551615") (vec (repeat 8 255))]]]
   (let [ctx (prepare [(ext "host" descriptor)
                      (c/decl "apply-scalar" [(c/p 1 "object")] "object"
                              (c/let-ir 2 "object" {:pap {:c (c/name-ir "host") :ys []}}
                                (c/let-ir 3 "object" {:ap {:x {:idx 2} :ys [(c/v 1)]}} (c/ret 3))))] [descriptor])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "apply-scalar" [0])
      (j/resume-host! ctx engine (request! ctx engine) reply)
      (let [value (finish! ctx engine)]
        ;; U32 uses an immediate boxed value; USize uses its boxed payload node.
        (is (= expected (if (= "usize" (:result descriptor))
                          (:scalar-bytes (j/java-value ctx value)) value)))
        (j/release! ctx engine value))
      (finally (j/close! ctx engine))))))

(deftest nullary-host-entry-is-not-an-initialized-constant-cache
  (let [zero (spec "research_zero" [] [] "object") ctx (prepare [(ext "host" zero)] [zero])
        engine (j/machine ctx)]
    (try
      (doseq [answer [41 42]]
        (j/start! ctx engine "host" [])
        (let [request (j/host-request ctx engine)]
          (is (some? request)) (is (empty? (args request)))
          (j/resume-host! ctx engine request answer)
          (is (= answer (j/take-result! ctx engine)))))
      (finally (j/close! ctx engine)))))

(deftest synchronous-invoke-exposes-suspension-and-does-not-spin
  (let [ctx (prepare [(ext "host" owned)] [owned]) engine (j/machine ctx)]
    (try
      (is (re-find #"(?i)host" (c/failure #(j/call ctx engine "host" [41]))))
      (is (= "host-call" (j/phase ctx engine)))
      (j/resume-host! ctx engine (j/host-request ctx engine) 42)
      (is (= 42 (j/take-result! ctx engine)))
      (finally (j/close! ctx engine)))))

(deftest host-failure-is-terminal-and-retains-the-original-cause
  (let [ctx (prepare [(ext "host" owned)] [owned]) engine (j/machine ctx)
        cause (ex-info "explicit host failure" {:probe true})]
    (j/start! ctx engine "host" [0])
    (j/fail-host! ctx engine (j/host-request ctx engine) cause)
    (is (= "failed" (j/phase ctx engine)))
    (is (identical? cause (j/host-failure ctx engine)))
    (is (nil? (j/host-request ctx engine)))
    (is (not= "NO ERROR" (c/failure #(j/advance! ctx engine 1))))
    (is (re-find #"(?i)fork|boundary" (c/failure #(j/fork! ctx engine []))))
    (is (re-find #"ownership cleanup" (c/failure #(j/close! ctx engine))))))

(deftest registry-is-exact-opt-in-and-allows-disjoint-captured-abis
  (let [other (spec "research_host" ["uint32"] [false] "uint32")
        rows [(ext "object-host" owned) (ext "scalar-host" other)]]
    (is (some? (:program (prepare rows [owned other]))))
    (doseq [[rs descriptors] [[rows [owned]]
                              [[(ext "host" owned)] [owned owned]]
                              [[(ext "host" (assoc owned :borrowed [true]))] [owned]]
                              [[(ext "host" owned)] [(assoc owned :symbol "lean_nat_add")]]]]
      (is (not= "NO ERROR" (c/failure #(prepare rs descriptors)))))
    (is (not= "NO ERROR" (c/failure #(prepare [(ext "host" owned)] [])))))
  (doseq [bad [(assoc owned :parameters ["uint64"])
               (assoc owned :parameters ["garbage"])
               (assoc owned :borrowed [])
               (assoc owned :symbol "")]]
    (is (not= "NO ERROR" (c/failure #(prepare [(ext "host" owned)] [bad]))))))

(deftest recursive-driver-rejects-host-execution
  (let [ctx (prepare [(ext "host" owned)] [owned]) engine (j/machine (dissoc ctx :explicit))]
    (is (re-find #"(?i)host|explicit" (c/failure #(j/call ctx engine "host" [0]))))
    ;; Root rejection precedes ownership transfer or any guest activation.
    (j/close! ctx engine)))

(defn fresh-object []
  (c/decl "fresh" [(c/p 1 "uint8")] "object"
          (c/let-ir 2 "object" (c/ctor 7 ["erased"] 0) (c/ret 2))))

(deftest invalid-object-and-insufficient-borrowed-reply-credits-do-not-claim
  (let [ctx (prepare [(fresh-object) (ext "host" borrowed)] [borrowed])
        engine (j/machine ctx) value (j/call ctx engine "fresh" [0])]
    (try
      (j/start! ctx engine "host" [value])
      (let [request (j/host-request ctx engine)]
        (doseq [reply [nil (Object.) :not-a-guest-value value]]
          (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine request reply))))
          (is (identical? request (j/host-request ctx engine)))
          (is (= 1 (c/rc ctx value))))
        (j/retain! ctx engine value)
        (j/resume-host! ctx engine request value)
        (is (identical? value (j/take-result! ctx engine)))
        (is (= 1 (c/rc ctx value)))
        (j/release! ctx engine value)
        (is (= 0 (c/rc ctx value))))
      (finally (j/close! ctx engine)))))

(deftest claimed-adapter-destructor-failure-retains-reply-and-uncertain-credit
  ;; Deliberately malformed host graph: this tests failure accounting rather
  ;; than asserting admission of arbitrary Java Node graphs.
  (let [ctx (prepare [(fresh-object) (ext "host" borrowed)] [borrowed])
        engine (j/machine ctx) parent (j/call ctx engine "fresh" [0])
        dead (j/call ctx engine "fresh" [0])]
    (j/release! ctx engine dead)
    (aset ^objects (.get ^java.lang.reflect.Field (:fields ctx) parent) 0 dead)
    (j/start! ctx engine "host" [parent])
    (let [request (j/host-request ctx engine) call (private-value request "call")]
      (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine request 7))))
      (is (= "failed" (j/phase ctx engine)))
      (is (true? (private-value call "replyClaimed")))
      (is (= 0 (private-value call "borrowedCursor")))
      (is (true? (private-value call "adapterReleaseStarted")))
      (is (true? (private-value call "resultOwned")))
      (is (= 7 (private-value call "completionResult")))
      (is (identical? request (private-value engine "failedHostRequest")))
      (is (some? (j/host-failure ctx engine)))
      (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine request 8))))
      (is (re-find #"ownership cleanup" (c/failure #(j/close! ctx engine)))))))

(deftest claimed-overapplication-failure-preserves-the-owned-reply
  (let [ctx (prepare [(ext "host" owned)
                      (c/decl "over" [(c/p 1 "object") (c/p 2 "object")] "object"
                              (c/let-ir 3 "object" {:pap {:c (c/name-ir "host") :ys []}}
                                (c/let-ir 4 "object" {:ap {:x {:idx 3} :ys [(c/v 1) (c/v 2)]}} (c/ret 4))))] [owned])
        engine (j/machine ctx)]
    (j/start! ctx engine "over" [0 42])
    (let [request (request! ctx engine) call (private-value request "call")]
      ;; A valid owned object-lane reply can still fail when AP requires closure.
      (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine request 7))))
      (is (= "failed" (j/phase ctx engine)))
      (is (true? (private-value call "replyClaimed")))
      (is (true? (private-value call "resultOwned")))
      (is (false? (private-value call "resultTransferStarted")))
      (is (= 7 (private-value call "completionResult")))
      (is (= [42] (vec (private-value call "surplus"))))
      (is (some? (j/host-failure ctx engine)))
      (is (not= "NO ERROR" (c/failure #(j/resume-host! ctx engine request 8))))
      (is (re-find #"ownership cleanup" (c/failure #(j/close! ctx engine)))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-host-checks)))
