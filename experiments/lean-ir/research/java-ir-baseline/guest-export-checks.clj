(ns java-ir-guest-export-checks
  "Immutable authenticated guest export dispatch; bounded synthetic owner models."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.edn :as edn]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [java-ir-generation-checks :as g] [java-ir-header-checks :as headers]
            [java-ir-code-checks :as code] [java-ir-continuation-checks :as k]
            [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(defn ext [label params result]
  (h/ext label (h/spec (str "guest_" label) params (vec (repeat (count params) false)) result)))
(defn setup
  ([rows] (setup rows []))
  ([rows host-specs]
   (let [base (j/prepare-host-program *basis* [] host-specs) source (j/source-binding base (Object.))
         hs (into {} (for [row rows] [(last (:name row)) (headers/header source row)]))]
     {:ctx (assoc (j/register-headers base (vec (vals hs))) :explicit (:explicit *basis*))
      :source source :headers hs})))
(defn materialize [ctx header row deps] (j/materialize-body ctx header (first (x/raw [row])) deps))
(defn slots [ctx field] (h/private-value (:program ctx) field))
(def identity-row (c/decl "impl" [(c/p 9 "object")] "object" (c/ret 9)))
(def origin-row (ext "forward" ["object"] "object"))
(def fresh-row (c/decl "fresh" [(c/p 1 "object")] "object"
                (c/let-ir 2 "object" (c/ctor 0 [] 1) (c/ret 2))))
(defn identity-context []
  (let [{:keys [ctx headers] :as data} (setup [origin-row identity-row])
        ready (materialize ctx (headers "impl") identity-row [])]
    (assoc data :ctx ready :bound (j/bind-guest-exports ready [[(headers "forward") (headers "impl")]]))))

(deftest binding-is-transactional-idempotent-and-never-publishes-alias-body
  (let [{:keys [ctx bound headers]} (identity-context)
        other-row (c/decl "other" [(c/p 7 "object")] "object" (c/ret 7))
        ;; Actual same-source alternate for a rebind attempt.
        source (.source (headers "impl")) other (headers/header source other-row)
        extended (j/register-headers bound [other])
        unbound-extended (j/register-headers ctx [other])
        a (j/function-id ctx "forward") b (j/function-id ctx "impl")]
    (is (nil? (aget (slots ctx "guestExports") a)))
    (is (identical? (aget (slots ctx "functions") b) (aget (slots bound "guestExports") a)))
    (is (nil? (aget (slots bound "preparedBodies") a)))
    (is (identical? (aget (slots ctx "preparedBodies") b) (aget (slots bound "preparedBodies") b)))
    (is (identical? (:program bound) (:program (j/bind-guest-exports bound [[(headers "forward") (headers "impl")]]))))
    (is (g/bad? #(j/bind-guest-exports extended [[(headers "forward") other]])))
    (is (g/bad? #(j/bind-guest-exports unbound-extended [[(headers "forward") (headers "impl")] [(headers "forward") other]])))
    (is (nil? (aget (slots ctx "guestExports") a)))
    (is (g/bad? #(j/bind-guest-exports ctx [[nil (headers "impl")]])))
    (is (g/bad? #(j/bind-guest-exports ctx [[(headers "forward") (headers "impl") :extra]])))
    (is (g/bad? #(j/bind-guest-exports ctx nil)))
    (is (identical? (:program ctx) (:program (j/bind-guest-exports ctx []))))))

(deftest raw-lane-result-borrow-and-arity-mismatches-reject-even-same-obj-lane
  (doseq [[params result borrow] [[["tobject"] "object" false]
                                  [["object"] "tobject" false]
                                  [["object"] "object" true]
                                  [["object" "object"] "object" false]]]
    (let [target (c/decl "different" (mapv #(assoc (c/p (+ 7 %1) %2) :borrow borrow) (range) params)
                        result (c/ret 7))
          {:keys [ctx headers]} (setup [origin-row target])]
      (is (re-find #"raw ABI mismatch" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") (headers "different")]]))))))
  (let [origin (ext "unsupported" ["float32"] "float32")
        target (c/decl "unsupported-body" [(c/p 9 "float32")] "float32" (c/ret 9))
        {:keys [ctx headers]} (setup [origin target])]
    (is (re-find #"Unsupported execution lane" (c/failure #(j/bind-guest-exports ctx [[(headers "unsupported") (headers "unsupported-body")]]))))))

(deftest exact-registration-source-direct-fdecl-and-nonnullary-profile
  (let [{:keys [ctx headers source]} (setup [origin-row identity-row])
        foreign (headers/header (j/source-binding ctx (Object.)) (c/decl "foreign" [(c/p 1 "object")] "object" (c/ret 1)))
        ctx (j/register-headers ctx [foreign])
        clone (headers/header source identity-row)]
    (is (re-find #"not registered" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") clone]]))))
    (is (re-find #"source binding differs" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") foreign]]))))
    (is (re-find #"direct fdecl" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") (headers "forward")]]))))
    (is (re-find #"extern origin" (c/failure #(j/bind-guest-exports ctx [[(headers "impl") (headers "impl")]])))))
  (let [origin (ext "empty-forward" [] "object")
        target (c/object-constant "empty-impl")
        {:keys [ctx headers]} (setup [origin target])]
    (is (re-find #"Nullary or initialized" (c/failure #(j/bind-guest-exports ctx [[(headers "empty-forward") (headers "empty-impl")]]))))))

(deftest reserved-and-host-symbols-cannot-be-shadowed-in-either-direction
  (let [bad (h/ext "forward" (h/spec "" ["object"] [false] "object"))
        {:keys [ctx headers]} (setup [bad identity-row])]
    (is (re-find #"Invalid guest export symbol" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]])))))
  (let [reserved (h/ext "forward" (h/spec "lean_nat_add" ["object"] [false] "object"))
        {:keys [ctx headers]} (setup [reserved identity-row])]
    (is (re-find #"cannot shadow builtin" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]])))))
  (let [spec (h/spec "guest_forward" ["object"] [false] "object")
        {:keys [ctx headers]} (setup [origin-row identity-row] [spec])]
    (is (re-find #"conflicts with host extern" (c/failure #(j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]])))))
  (let [{:keys [bound]} (identity-context) spec (h/spec "guest_forward" ["object"] [false] "object")]
    (is (re-find #"conflicts with guest export" (c/failure #(j/register-headers bound [] [spec]))))
    (is (re-find #"conflicts with guest export" (c/failure #(j/extend-program bound [] [spec]))))))

(deftest root-and-direct-fap-use-real-target-variable-ids-and-owner-dispositions
  (let [origin (ext "forward-two" ["object" "object"] "object")
        target (c/decl "impl-two" [(c/p 9 "object") (c/p 4 "object")] "object"
                 ["dec" {:idx 9} 1 true false (c/ret 4)])
        caller (c/decl "caller" [(c/p 7 "object") (c/p 8 "object")] "object"
                 (c/let-ir 20 "object" (c/fap "forward-two" [(c/v 8) (c/v 7)]) (c/ret 20)))
        {:keys [ctx headers]} (setup [origin target caller])
        ctx (materialize ctx (headers "impl-two") target [])
        ctx (materialize ctx (headers "caller") caller [(headers "forward-two")])
        ctx (j/extend-program ctx (x/raw [fresh-row]))
        bound (j/bind-guest-exports ctx [[(headers "forward-two") (headers "impl-two")]])
        engine (j/machine ctx) a (j/call ctx engine "fresh" [0]) b (j/call ctx engine "fresh" [0])]
    (try
      (is (re-find #"Extern implementation unavailable" (c/failure #(j/call ctx engine "forward-two" [a b]))))
      (is (= 1 (c/rc ctx a) (c/rc ctx b)))
      (j/install-program! bound engine)
      (is (identical? b (j/call bound engine "forward-two" [a b])))
      (is (h/private-value a "dead")) (is (= 1 (c/rc ctx b)))
      (j/release! bound engine b)
      (let [a (j/call bound engine "fresh" [0]) b (j/call bound engine "fresh" [0])]
        (is (identical? a (j/call bound engine "caller" [a b])))
        (is (h/private-value b "dead")) (is (= 1 (c/rc ctx a))) (j/release! bound engine a))
      (finally (j/close! bound engine)))))

(deftest matching-borrow-abi-preserves-owned-guest-wrapper-direct-call-accounting
  (let [origin (h/ext "borrow-forward" (h/spec "guest_borrow" ["object"] [true] "object"))
        impl (c/decl "borrow-impl" [(assoc (c/p 19 "object") :borrow true)] "object"
               ["inc" {:idx 19} 1 true false (c/ret 19)])
        wrapper (c/decl "owned-wrapper" [(c/p 7 "object")] "object"
                  (c/let-ir 8 "object" (c/fap "borrow-forward" [(c/v 7)])
                    ["dec" {:idx 7} 1 true false (c/ret 8)]))
        {:keys [ctx headers]} (setup [origin impl wrapper])
        ctx (materialize ctx (headers "borrow-impl") impl [])
        ctx (materialize ctx (headers "owned-wrapper") wrapper [(headers "borrow-forward")])
        ctx (j/bind-guest-exports ctx [[(headers "borrow-forward") (headers "borrow-impl")]])
        ctx (j/extend-program ctx (x/raw [fresh-row])) engine (j/machine ctx)
        value (j/call ctx engine "fresh" [0])
        before [(h/private-value engine "retains") (h/private-value engine "releases")]]
    (try
      (is (identical? value (j/call ctx engine "owned-wrapper" [value])))
      (is (= 1 (c/rc ctx value)))
      (is (= 1 (- (h/private-value engine "retains") (first before))))
      (is (= 1 (- (h/private-value engine "releases") (second before))))
      (j/release! ctx engine value)
      (is (h/private-value value "dead"))
      (finally (j/close! ctx engine)))))

(deftest positive-unboxed-lanes-use-actual-target-registers-on-root-and-fap
  (let [origin (ext "scalar-forward" ["uint32"] "uint32")
        impl (c/decl "scalar-impl" [(c/p 17 "uint32")] "uint32" (c/ret 17))
        caller (c/decl "scalar-caller" [(c/p 9 "uint32")] "uint32"
                 (c/let-ir 25 "uint32" (c/fap "scalar-forward" [(c/v 9)]) (c/ret 25)))
        {:keys [ctx headers]} (setup [origin impl caller])
        ctx (materialize ctx (headers "scalar-impl") impl [])
        ctx (materialize ctx (headers "scalar-caller") caller [(headers "scalar-forward")])
        ctx (j/bind-guest-exports ctx [[(headers "scalar-forward") (headers "scalar-impl")]]) engine (j/machine ctx)]
    (try
      (doseq [value [0 1 0x80000000 0xffffffff]]
        (is (= value (j/call ctx engine "scalar-forward" [value])))
        (is (= value (j/call ctx engine "scalar-caller" [value]))))
      (finally (j/close! ctx engine)))))

(deftest ordinary-recursion-through-alias-uses-real-self-tail-frame
  (let [origin (ext "count-down" ["tobject"] "tobject")
        sub (h/ext "subtract" (h/spec "lean_nat_sub" ["tobject" "tobject"] [true true] "tobject"))
        target (c/decl "count-impl" [(c/p 9 "tobject")] "tobject"
                 ["case" (c/name-ir "Nat") {:idx 9} "tobject"
                  [["ctor" {:cidx 0} (c/ret 9)]
                   ["default" (c/let-ir 10 "tobject" (c/lit 1)
                                (c/let-ir 11 "tobject" (c/fap "subtract" [(c/v 9) (c/v 10)])
                                  (c/let-ir 12 "tobject" (c/fap "count-down" [(c/v 11)]) (c/ret 12))))]]])
        {:keys [ctx headers]} (setup [origin sub target])
        ctx (materialize ctx (headers "count-impl") target [(headers "count-down") (headers "subtract")])
        ctx (j/bind-guest-exports ctx [[(headers "count-down") (headers "count-impl")]]) engine (j/machine ctx)]
    (try
      (is (= 0 (j/call ctx engine "count-down" [5000])))
      (is (nil? (aget (slots ctx "preparedBodies") (j/function-id ctx "count-down"))))
      (finally (j/close! ctx engine)))))

(deftest ancestor-closures-and-parent-sibling-forks-see-only-their-program-binding
  (let [{:keys [ctx bound headers source]} (identity-context) parent (j/machine ctx)
        closure (j/make-closure! ctx parent "forward" [])
        child (j/fork! ctx parent [closure]) sibling (j/fork! ctx parent [closure])
        a (:engine child) b (:engine sibling)
        bound (j/extend-program bound (x/raw [(second g/common)]))
        other-row (c/decl "other" [(c/p 77 "object")] "object"
                    ["dec" {:idx 77} 1 true false
                     (c/let-ir 78 "object" (c/lit 99) (c/ret 78))])
        other (headers/header source other-row)
        alternate (j/register-headers ctx [other])
        alternate (materialize alternate other other-row [])
        alternate (j/bind-guest-exports alternate [[(headers "forward") other]])
        alternate (j/extend-program alternate (x/raw [(second g/common)]))]
    (try
      (j/install-program! bound a) (j/install-program! alternate b)
      (is (= 42 (j/call bound a "apply" [(first (:roots child)) 42])))
      (is (= 99 (j/call alternate b "apply" [(first (:roots sibling)) 42])))
      (is (re-find #"Extern implementation unavailable" (c/failure #(j/call ctx parent "forward" [7]))))
      (is (identical? (:program ctx) (h/private-value parent "program")))
      (is (g/bad? #(j/install-program! bound b)))
      (is (identical? (:program alternate) (h/private-value b "program")))
      (j/release! ctx parent closure)
      (finally (j/close! bound a) (j/close! ctx parent) (j/close! alternate b)))))

(deftest partial-application-keeps-origin-capture-order-across-fork
  (let [origin (ext "pair-forward" ["object" "object"] "object")
        target (c/decl "pair-impl" [(c/p 23 "object") (c/p 7 "object")] "object"
                 ["dec" {:idx 23} 1 true false (c/ret 7)])
        {:keys [ctx headers]} (setup [origin target])
        ctx (materialize ctx (headers "pair-impl") target [])
        ctx (j/bind-guest-exports ctx [[(headers "pair-forward") (headers "pair-impl")]])
        ctx (j/extend-program ctx (x/raw [(second g/common) fresh-row])) engine (j/machine ctx)
        captured (j/call ctx engine "fresh" [0]) partial (j/make-closure! ctx engine "pair-forward" [captured])
        child (j/fork! ctx engine [partial]) child-engine (:engine child)]
    (try
      (is (= "pair-forward" (h/private-value (h/private-value partial "closure") "label")))
      (is (= 42 (j/call ctx engine "apply" [partial 42])))
      (is (= 43 (j/call ctx child-engine "apply" [(first (:roots child)) 43])))
      (is (h/private-value captured "dead"))
      (finally (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest oversaturated-application-resumes-real-target-then-applies-surplus
  (let [target (c/decl "impl" [(c/p 19 "object")] "object"
                 ["dec" {:idx 19} 1 true false
                  (c/let-ir 20 "object" {:pap {:c (c/name-ir "identity") :ys []}} (c/ret 20))])
        identity (c/decl "identity" [(c/p 31 "object")] "object" (c/ret 31))
        caller (c/decl "over" [(c/p 1 "object")] "object"
                 (c/let-ir 2 "object" {:pap {:c (c/name-ir "forward") :ys []}}
                   (c/let-ir 3 "object" {:ap {:x {:idx 2} :ys ["erased" (c/v 1)]}} (c/ret 3))))
        {:keys [ctx headers]} (setup [origin-row target identity caller])
        ctx (materialize ctx (headers "over") caller [(headers "forward")])
        ctx (j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]])
        first-ready (materialize ctx (headers "impl") target [(headers "identity")])
        ready (materialize first-ready (headers "identity") identity [])
        engine (j/machine (if (:explicit ctx) ctx ready))]
    (try
      (if (:explicit ctx)
        (do
          (j/start! ctx engine "over" [42])
          (let [request (code/request! ctx engine)]
            (is (identical? (headers "impl") (j/request-value request "header")))
            (is (= [0] (code/args request)))
            (j/resume-code! first-ready engine request)
            (let [second-request (code/request! first-ready engine)]
              (is (identical? (headers "identity") (j/request-value second-request "header")))
              (is (= [42] (code/args second-request)))
              (j/resume-code! ready engine second-request)
              (is (= 42 (code/finish! ready engine))))))
        (is (= 42 (j/call ready engine "over" [42]))))
      (finally (j/close! ready engine)))))

(deftest failed-full-ap-preflight-preserves-original-capture-owners
  (let [origin (ext "pair-forward" ["object" "object"] "object")
        {:keys [ctx]} (setup [origin])
        ctx (j/extend-program ctx (x/raw [(second g/common) fresh-row])) engine (j/machine ctx)
        captured (j/call ctx engine "fresh" [0])
        closure (j/make-closure! ctx engine "pair-forward" [captured])]
    (is (re-find #"Extern implementation unavailable" (c/failure #(j/call ctx engine "apply" [closure 42]))))
    (is (= 1 (c/rc ctx closure) (c/rc ctx captured)))
    (is (false? (h/private-value closure "dead")))
    (is (false? (h/private-value captured "dead")))
    (if (:explicit ctx)
      (is (g/bad? #(j/close! ctx engine)))
      (do (j/release! ctx engine closure) (j/close! ctx engine)))))

(deftest explicit-code-request-targets-implementation-once-and-forks-owners
  (let [{:keys [ctx headers]} (setup [origin-row identity-row])
        bound (assoc (j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]]) :explicit true)
        ready (materialize bound (headers "impl") identity-row []) engine (j/machine bound)]
    (j/start! bound engine "forward" [42])
    (let [request (j/code-request bound engine) child (:engine (j/fork! bound engine []))
          child-request (j/code-request bound child)]
      (try
        (is (identical? (headers "impl") (j/request-value request "header")))
        (is (= [42] (code/args request)))
        (is (nil? (aget (slots ready "preparedBodies") (j/function-id ready "forward"))))
        (is (g/bad? #(j/resume-code! bound engine request)))
        (is (identical? request (j/code-request bound engine)))
        (is (g/bad? #(j/resume-code! ready child request)))
        (j/resume-code! ready engine request) (j/resume-code! ready child child-request)
        (is (= 42 (code/finish! ready engine) (code/finish! ready child)))
        (is (g/bad? #(j/resume-code! ready engine request)))
        (finally (j/close! ready engine) (j/close! ready child))))))

(deftest actual-host-suspension-inside-guest-body-keeps-export-dispatch-separate
  (let [spec (h/spec "actual_host" ["object"] [false] "object")
        native (h/ext "native" spec)
        impl (c/decl "impl" [(c/p 17 "object")] "object"
               (c/let-ir 18 "object" (c/fap "native" [(c/v 17)]) (c/ret 18)))
        {:keys [ctx headers]} (setup [origin-row native impl] [spec])
        ctx (assoc (materialize ctx (headers "impl") impl [(headers "native")]) :explicit true)
        ctx (j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]])
        ctx (j/extend-program ctx (x/raw [fresh-row])) engine (j/machine ctx)
        value (j/call ctx engine "fresh" [0])]
    (j/start! ctx engine "forward" [value])
    (loop [left 20]
      (when (zero? left) (throw (ex-info "host request not reached" {})))
      (when-not (j/host-request ctx engine) (j/advance! ctx engine 1) (recur (dec left))))
    (let [request (j/host-request ctx engine) child (:engine (j/fork! ctx engine []))
          child-request (j/host-request ctx child)
          child-value (first (vec (j/request-value child-request "arguments")))]
      (try
        (is (= "actual_host" (j/request-value request "symbol")))
        (is (identical? value (first (vec (j/request-value request "arguments")))))
        (is (not (identical? value child-value)))
        (is (= 1 (c/rc ctx value) (c/rc ctx child-value)))
        (j/resume-host! ctx engine request value) (j/resume-host! ctx child child-request child-value)
        (is (identical? value (code/finish! ctx engine)))
        (is (identical? child-value (code/finish! ctx child)))
        (j/release! ctx engine value) (j/release! ctx child child-value)
        (finally (j/close! ctx engine) (j/close! ctx child))))))

(deftest nullary-cache-owners-remain-on-real-constant-not-nonnullary-alias
  (let [constant (c/object-constant "constant")
        impl (c/decl "impl" [(c/p 9 "object")] "object"
               (c/let-ir 10 "object" (c/fap "constant" [])
                 ["inc" {:idx 10} 1 true false (c/ret 10)]))
        {:keys [ctx headers]} (setup [origin-row impl constant])
        ctx (materialize ctx (headers "constant") constant [])
        ctx (materialize ctx (headers "impl") impl [(headers "constant")])
        ctx (j/bind-guest-exports ctx [[(headers "forward") (headers "impl")]]) engine (j/machine ctx)]
    (try
      (let [value (j/call ctx engine "forward" [0])]
        (is (= 2 (c/rc ctx value))) (j/release! ctx engine value))
      (is (false? (aget ^booleans (h/private-value engine "constantReady") (j/function-id ctx "forward"))))
      (is (false? (aget ^booleans (h/private-value engine "constantReady") (j/function-id ctx "impl"))))
      (is (true? (aget ^booleans (h/private-value engine "constantReady") (j/function-id ctx "constant"))))
      (let [child (:engine (j/fork! ctx engine []))]
        (try
          (let [a (j/call ctx engine "forward" [0]) b (j/call ctx child "forward" [0])]
            (is (not (identical? a b))) (is (= 2 (c/rc ctx a) (c/rc ctx b)))
            (j/release! ctx engine a) (j/release! ctx child b))
          (finally (j/close! ctx child))))
      (finally (j/close! ctx engine)))))

(deftest certified-pointer-sites-remain-bound-to-the-real-implementation-body
  (let [origin (ext "compare-forward" ["object" "object"] "uint8")
        address (h/ext "address" (h/spec "lean_ptr_addr" ["erased" "tobject"] [false true] "usize"))
        eq (h/ext "same-word" (h/spec "lean_usize_dec_eq" ["usize" "usize"] [false false] "uint8"))
        impl (c/decl "compare-impl" [(c/p 23 "object") (c/p 7 "object")] "uint8"
               (c/let-ir 24 "usize" (c/fap "address" ["erased" (c/v 23)])
                 (c/let-ir 25 "usize" (c/fap "address" ["erased" (c/v 7)])
                   (c/let-ir 26 "uint8" (c/fap "same-word" [(c/v 24) (c/v 25)])
                     ["dec" {:idx 23} 1 false false ["dec" {:idx 7} 1 false false (c/ret 26)]]))))
        {:keys [ctx headers]} (setup [origin address eq impl])
        ctx (materialize ctx (headers "compare-impl") impl [(headers "address") (headers "same-word")])
        ctx (j/bind-guest-exports ctx [[(headers "compare-forward") (headers "compare-impl")]])
        ctx (j/extend-program ctx (x/raw [fresh-row])) engine (j/machine ctx)]
    (try
      (let [same (j/call ctx engine "fresh" [0])]
        (j/retain! ctx engine same)
        (is (= 1 (j/call ctx engine "compare-forward" [same same])))
        (is (h/private-value same "dead")))
      (let [a (j/call ctx engine "fresh" [0]) b (j/call ctx engine "fresh" [0])]
        (is (= 0 (j/call ctx engine "compare-forward" [a b])))
        (is (h/private-value a "dead")) (is (h/private-value b "dead")))
      (is (nil? (aget (slots ctx "preparedBodies") (j/function-id ctx "compare-forward"))))
      (finally (j/close! ctx engine)))))

(deftest authentic-meta-export-pairs-request-exact-implementation-before-context-execution
  (let [fixture "test/fixtures/java-guest-export-runtime/original-rows.json"
        originals (json/read-str (slurp fixture))
        manifest (edn/read-string (slurp "test/fixtures/java-guest-export-runtime/provenance.edn"))]
    (is (= (:fixture-sha256 manifest) (corpus/sha256 fixture))) (is (= 8 (count originals)))
    (doseq [[origin-label impl-label] [["Lean.Meta.whnf" "Lean.Meta.whnfImp"]
                                     ["Lean.Meta.inferType" "Lean.Meta.inferTypeImp"]]
            :let [origin (first (filter #(= origin-label (get % "label")) originals))
                  impl (first (filter #(= impl-label (get % "label")) originals))
                  base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
                  a (j/declaration-header source (get origin "row") (get origin "sha256"))
                  b (j/declaration-header source (get impl "row") (get impl "sha256"))
                  ctx (j/bind-guest-exports (j/register-headers base [a b]) [[a b]]) engine (j/machine ctx)]]
      ;; These unused carrier placeholders only populate the suspended activation.
      ;; No MetaM context is asserted valid and no implementation body is entered.
      (j/start! ctx engine origin-label [0 0 0 0 0 0])
      (let [request (j/code-request ctx engine)]
        (is (identical? b (j/request-value request "header")))
        (is (= (get impl "sha256") (.originalSha256 ^Object (j/request-value request "header"))))
        (is (= 0 (j/instructions ctx engine)))
        (is (every? nil? (seq (slots ctx "preparedBodies"))))
        (j/fail-code! ctx engine request (ex-info "metadata-only request gate stops before MetaM body" {}))
        (is (= "failed" (j/phase ctx engine)))
        (is (g/bad? #(j/close! ctx engine)))))))

(deftest original-boxed-meta-wrappers-reach-the-same-authenticated-implementation-header
  (let [originals (json/read-str (slurp "test/fixtures/java-guest-export-runtime/original-rows.json"))]
    (doseq [[origin-label impl-label] [["Lean.Meta.whnf" "Lean.Meta.whnfImp"]
                                     ["Lean.Meta.inferType" "Lean.Meta.inferTypeImp"]]
            :let [by-label (into {} (map #(vector (get % "label") %) originals))
                  origin (by-label origin-label) impl (by-label impl-label)
                  wrapper (by-label (str origin-label "._boxed"))
                  base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
                  a (j/declaration-header source (get origin "row") (get origin "sha256"))
                  b (j/declaration-header source (get impl "row") (get impl "sha256"))
                  w (j/declaration-header source (get wrapper "row") (get wrapper "sha256"))
                  ctx (j/register-headers base [a b w])
                  ctx (j/materialize-body ctx w (get wrapper "row") [a])
                  ctx (j/bind-guest-exports ctx [[a b]]) engine (j/machine ctx)]]
      ;; Only the authentic forwarding wrapper runs; implementation remains absent.
      (j/start! ctx engine (str origin-label "._boxed") [0 0 0 0 0 0])
      (let [request (code/request! ctx engine)]
        (is (identical? b (j/request-value request "header")))
        (is (= (get impl "sha256") (.originalSha256 ^Object (j/request-value request "header"))))
        (is (= [0 0 0 0 0 0] (code/args request)))
        (is (= 1 (j/instructions ctx engine)))
        (is (nil? (aget (slots ctx "preparedBodies") (j/function-id ctx origin-label))))
        (j/fail-code! ctx engine request (ex-info "stop before MetaM context execution" {}))
        (is (g/bad? #(j/close! ctx engine)))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-guest-export-checks)))
