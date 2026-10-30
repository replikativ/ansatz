(ns java-ir-code-checks
  "Demand-code control and ownership; bounded retained-REPL programs."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [java-ir-host-checks :as h]
            [java-ir-generation-checks :as g]
            [java-ir-header-checks :as headers]
            [java-ir-continuation-checks :as k]))
(def ^:dynamic *basis* nil)
(defn setup [rows]
  (let [base (j/prepare-host-program *basis* [] []) binding (j/source-binding base (Object.))
        descriptors (into {} (for [row rows] [(last (:name row)) (headers/header binding row)]))]
    {:ctx (j/register-headers base (vec (vals descriptors))) :headers descriptors}))
(defn materialize [ctx target row deps]
  (j/materialize-body ctx target (first (x/raw [row])) deps))
(defn request! [ctx engine]
  (loop [left 100]
    (when (zero? left) (throw (ex-info "No code suspension" {})))
    (if-let [request (j/code-request ctx engine)] request
      (do (assert (not (j/advance! ctx engine 1))) (recur (dec left))))))
(defn args [request] (vec (j/request-value request "arguments")))
(defn finish! [ctx engine] (k/finish! ctx engine [1 3 7]))
(def identity-row headers/identity-row)

(deftest root-demand-is-once-only-and-rejected-descendants-do-not-install
  (let [{:keys [ctx headers]} (setup [identity-row]) engine (j/machine ctx)
        ready (materialize ctx (headers "identity") identity-row [])
        insufficient (j/extend-program ctx (x/raw [(g/literal "unrelated" 99)]))]
    (try
      (j/start! ctx engine "identity" [42])
      (let [request (j/code-request ctx engine) before (k/counters ctx engine)]
        (is (= "code-call" (j/phase ctx engine)))
        (is (= 0 (j/instructions ctx engine)))
        (is (identical? (headers "identity") (j/request-value request "header")))
        (is (= [42] (args request)))
        (aset ^objects (j/request-value request "arguments") 0 9)
        (is (= [42] (args request)))
        (is (false? (j/advance! ctx engine 100)))
        (is (= before (k/counters ctx engine)))
        (is (g/bad? #(j/resume-code! insufficient engine request)))
        (is (identical? (:program ctx) (h/private-value engine "program")))
        (is (identical? request (j/code-request ctx engine)))
        (j/install-program! ready engine)
        (is (identical? request (j/code-request ready engine)))
        (j/resume-code! ready engine request)
        (is (= 42 (finish! ready engine)))
        (is (g/bad? #(j/resume-code! ready engine request))))
      (finally (j/close! ready engine)))))

(deftest nested-call-demand-and-fork-preserve-caller-and-request-identities
  (let [caller (c/decl "caller" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" (c/fap "identity" [(c/v 1)]) (c/ret 2)))
        {:keys [ctx headers]} (setup [caller identity-row])
        linked (materialize ctx (headers "caller") caller [(headers "identity")])
        ready (materialize linked (headers "identity") identity-row [])
        parent (j/machine linked)]
    (j/start! linked parent "caller" [42])
    (let [request (request! linked parent) child (:engine (j/fork! linked parent []))
          child-request (j/code-request linked child)]
      (try
        (is (= 1 (j/depth linked parent) (j/depth linked child)))
        (is (not (identical? request child-request)))
        (is (= [42] (args request) (args child-request)))
        (is (g/bad? #(j/resume-code! ready child request)))
        (is (identical? child-request (j/code-request linked child)))
        (j/resume-code! ready parent request)
        (j/resume-code! ready child child-request)
        (is (= 42 (finish! ready parent) (finish! ready child)))
        (finally (j/close! ready parent) (j/close! ready child))))))

(deftest oversaturated-ap-can-demand-two-bodies-without-repeating-consumption
  (let [f (c/decl "first" [(c/p 1 "object")] "object"
                  (c/let-ir 2 "object" {:pap {:c (c/name-ir "identity") :ys []}} (c/ret 2)))
        {:keys [ctx headers]} (setup [f identity-row])
        ctx (j/extend-program ctx (x/raw [(c/decl "over" [(c/p 1 "object")] "object"
                       (c/let-ir 2 "object" {:pap {:c (c/name-ir "first") :ys []}}
                         (c/let-ir 3 "object" {:ap {:x {:idx 2} :ys ["erased" (c/v 1)]}}
                           (c/ret 3))))]))
        f-ready (materialize ctx (headers "first") f [(headers "identity")])
        both (materialize f-ready (headers "identity") identity-row []) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "over" [42])
      (let [a (request! ctx engine)]
        (is (identical? (headers "first") (j/request-value a "header")))
        (j/resume-code! f-ready engine a)
        (let [b (request! f-ready engine)]
          (is (identical? (headers "identity") (j/request-value b "header")))
          (is (= [42] (args b)))
          (j/resume-code! both engine b)
          (is (= 42 (finish! both engine)))
          (is (= 2 (h/private-value engine "shellDeletes")))))
      (finally (j/close! both engine)))))

(deftest shared-ap-capture-aliases-survive-code-pause-and-fork
  (let [target (c/decl "target" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))
        {:keys [ctx headers]} (setup [target])
        ctx (j/extend-program ctx (x/raw [(c/decl "fresh" [(c/p 1 "object")] "object"
                                      (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2)))
                                         (second g/common)]))
        ready (materialize ctx (headers "target") target []) parent (j/machine ctx)
        capture (j/call ctx parent "fresh" [0]) closure (j/make-closure! ctx parent "target" [capture])]
    (j/retain! ctx parent closure)
    (j/start! ctx parent "apply" [closure 42])
    (let [request (request! ctx parent)
          {:keys [engine roots]} (j/fork! ctx parent [closure capture])
          child engine [child-closure child-capture] roots child-request (j/code-request ctx child)]
      (try
        (is (= 1 (c/rc ctx closure) (c/rc ctx child-closure)))
        (is (= 2 (c/rc ctx capture) (c/rc ctx child-capture)))
        (is (identical? capture (first (args request))))
        (is (identical? child-capture (first (args child-request))))
        (j/resume-code! ready parent request) (j/resume-code! ready child child-request)
        (let [a (finish! ready parent) b (finish! ready child)]
          (is (identical? capture a)) (is (identical? child-capture b))
          (j/release! ready parent a) (j/release! ready child b))
        (j/release! ready parent closure) (j/release! ready child child-closure)
        (is (= 0 (c/rc ctx capture) (c/rc ctx child-capture)))
        (finally (j/close! ready parent) (j/close! ready child))))))

(deftest nullary-value-is-cached-before-any-subsequent-code-demand
  (let [row (c/object-constant "constant") {:keys [ctx headers]} (setup [row])
        ready (materialize ctx (headers "constant") row []) engine (j/machine ctx)]
    (try
      (j/start! ctx engine "constant" [])
      (j/resume-code! ready engine (j/code-request ctx engine))
      (let [a (finish! ready engine)]
        (is (= 2 (c/rc ready a)))
        (j/start! ready engine "constant" [])
        (is (= "complete" (j/phase ready engine)))
        (is (nil? (j/code-request ready engine)))
        (let [b (j/take-result! ready engine)]
          (is (identical? a b)) (is (= 3 (c/rc ready a)))
          (j/release! ready engine b))
        (j/release! ready engine a))
      (finally (j/close! ready engine)))))

(deftest scalar-code-request-keeps-original-typed-argument-and-result
  (let [row (c/decl "scalar" [(c/p 1 "uint32")] "uint32" (c/ret 1))
        {:keys [ctx headers]} (setup [row]) ready (materialize ctx (headers "scalar") row [])
        engine (j/machine ctx)]
    (try
      (j/start! ctx engine "scalar" [4294967295])
      (let [request (j/code-request ctx engine)]
        (is (= [4294967295] (args request)))
        (is (= ["uint32"] (vec (j/request-value request "paramTypes"))))
        (j/resume-code! ready engine request)
        (is (= 4294967295 (finish! ready engine))))
      (finally (j/close! ready engine)))))

(deftest explicit-loader-failure-is-terminal-and-cannot-be-replayed
  (let [{:keys [ctx]} (setup [identity-row]) engine (j/machine ctx)
        cause (ex-info "bounded loader failure" {})]
    (j/start! ctx engine "identity" [42])
    (let [request (j/code-request ctx engine)]
      (j/fail-code! ctx engine request cause)
      (is (= "failed" (j/phase ctx engine)))
      (is (identical? cause (j/code-failure ctx engine)))
      (is (identical? request (j/request-value engine "failureCodeRequest")))
      (is (g/bad? #(j/fail-code! ctx engine request cause)))
      (is (g/bad? #(j/resume-code! ctx engine request)))
      (is (g/bad? #(j/close! ctx engine))))))

(deftest host-reply-overapplication-can-transfer-into-code-demand-once
  (let [{:keys [ctx headers]} (setup [identity-row])
        ctx (j/extend-program ctx (x/raw [(h/ext "host" h/borrowed)
                    (c/decl "fresh" [(c/p 1 "object")] "object"
                            (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2)))
                    (c/decl "over" [(c/p 1 "object")] "object"
                            (c/let-ir 2 "object" {:pap {:c (c/name-ir "host") :ys []}}
                              (c/let-ir 3 "object" {:ap {:x {:idx 2} :ys [(c/v 1) "erased"]}}
                                (c/ret 3))))]) [h/borrowed])
        ready (materialize ctx (headers "identity") identity-row []) engine (j/machine ctx)
        value (j/call ctx engine "fresh" [0])]
    (try
      (j/start! ctx engine "over" [value])
      (let [host-request (h/request! ctx engine)]
        (j/resume-host! ctx engine host-request (j/make-closure! ctx engine "identity" []))
        (let [code-request (j/code-request ctx engine)]
          (is (= "code-call" (j/phase ctx engine)))
          (is (= 0 (c/rc ctx value)))
          (is (= [0] (args code-request)))
          (is (g/bad? #(j/resume-host! ctx engine host-request 0)))
          (j/resume-code! ready engine code-request)
          (is (= 0 (finish! ready engine)))
          (is (= 0 (c/rc ctx value)))))
      (finally (j/close! ready engine)))))

(deftest forked-demands-can-link-siblings-with-different-callee-ids
  (let [f (c/decl "caller" [(c/p 1 "object")] "object"
                  (c/let-ir 2 "object" (c/fap "identity" [(c/v 1)]) (c/ret 2)))
        base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        fh (headers/header source f) gh (headers/header source identity-row)
        ctx (j/register-headers base [fh])
        a (j/extend-program ctx (x/raw [(g/literal "pad-a" 1)]))
        b (j/extend-program ctx (x/raw [(g/literal "pad-b" 2) (g/literal "pad-c" 3)]))
        a (materialize (materialize a fh f [gh]) gh identity-row [])
        b (materialize (materialize b fh f [gh]) gh identity-row [])
        parent (j/machine ctx)]
    (j/start! ctx parent "caller" [42])
    (let [request (j/code-request ctx parent) child (:engine (j/fork! ctx parent []))]
      (try
        (is (not= (j/function-id a "identity") (j/function-id b "identity")))
        (j/resume-code! a parent request)
        (j/resume-code! b child (j/code-request ctx child))
        (is (= 42 (finish! a parent) (finish! b child)))
        (finally (j/close! a parent) (j/close! b child))))))

(deftest failure-after-code-claim-is-terminal-and-retains-original-request
  (let [{:keys [ctx headers]} (setup [identity-row])
        ready (materialize ctx (headers "identity") identity-row []) engine (j/machine ctx)]
    (j/start! ctx engine "identity" [42])
    (let [request (j/code-request ctx engine)
          ;; Fault injection: entry's tick fails after publication/claim.
          field (.getDeclaredField (class engine) "callsLeft")]
      (.setAccessible field true) (.setLong field engine -1)
      (is (g/bad? #(j/resume-code! ready engine request)))
      (is (= "failed" (j/phase ready engine)))
      (is (some? (j/code-failure ready engine)))
      (is (identical? request (j/request-value engine "failureCodeRequest")))
      (is (g/bad? #(j/resume-code! ready engine request)))
      (is (g/bad? #(j/close! ready engine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-code-checks)))
