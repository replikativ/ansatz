(ns java-ir-level-mvars-checks
  "Owned level substitution through authentic original helpers; no image required."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [java-ir-logical-sharing-checks :as sharing] [java-ir-code-checks :as code] [java-ir-header-checks :as headers] [java-ir-generation-checks :as g]
            [java-ir-expr-find-checks :as find] [java-ir-expr-equality-checks :as eq]
            [java-ir-sync-task-checks :as sync] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-level-mvars-runtime/")
(def roles ["Lean.getLevelMVarAssignmentExp" "Lean.assignLevelMVarExp"
            "Lean.Level.succ._override" "Lean.Level.max._override" "Lean.Level.imax._override"])
(defn records [] (json/read-str (slurp (str directory "execution-rows.json"))))
(defn fresh-context-row []
  ;; Test-only storage copy of the actual compiled 10-object-field context constructor.
  (let [tail (c/let-ir 12 "object" (c/ctor 0 (mapv c/v (range 2 12)) 0)
               ["dec" {:idx 1} 1 false false (c/ret 12)])]
    (c/decl "model-fresh-mctx" [(c/p 1 "object")] "object"
      (reduce (fn [body i]
                (c/let-ir (+ i 2) "object" {:proj {:i i :x {:idx 1}}}
                  ["inc" {:idx (+ i 2)} 1 false false body])) tail (reverse (range 10))))))
(defn setup-copy [label]
  ;; Authentic constructor/setter algorithm under a distinct MODEL name, so input
  ;; construction does not accidentally prepare the actual helper under test.
  (let [entry (first (filter #(= label (get % "label")) (records)))
        alias (str "model-setup-" label) n ["str" ["anonymous"] alias]]
    {"label" alias "sha256" headers/digest
     "row" (-> (get entry "row") (assoc "name" n) (assoc-in ["ir" "fdecl" "f"] n))}))
(defn context
  ([] (context {}))
  ([{:keys [defer inactive replacements rows host-specs tasks]}]
   (let [entries (concat (records) (eq/records)
                        (when tasks (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json")))
                        (for [r (x/raw rows)] {"label" (last (get r "name")) "row" r "sha256" headers/digest})
                        (map setup-copy (rest roles))
                        (for [r (x/raw [(fresh-context-row)])]
                          {"label" "model-fresh-mctx" "row" r "sha256" headers/digest}))
         entries (map (fn [r] (if-let [body (get replacements (get r "label"))]
                                (assoc-in r ["row" "ir" "fdecl" "body"] (json/read-str (json/write-str body))) r)) entries)
         entries (vals (reduce (fn [m r] (let [n (get-in r ["row" "name"])]
                                          (when-let [old (m n)] (assert (= (get old "row") (get r "row"))))
                                          (assoc m n r))) {} entries))
         base (j/prepare-host-program *basis* [] [])
         source (j/source-binding base {:level-mvars-fixture (corpus/sha256 (str directory "provenance.json")) :models true})
         hm (into {} (for [r entries] [(get-in r ["row" "name"]) (j/declaration-header source (get r "row") (get r "sha256"))]))
         registered (j/register-headers base (vec (vals hm)) (or host-specs []))
         ctx (reduce (fn [ctx r]
                       (if (and (get-in r ["row" "ir" "fdecl"]) (not (contains? (set defer) (get r "label"))))
                         (j/materialize-body ctx (hm (get-in r ["row" "name"])) (get r "row")
                           (mapv hm (find/direct (get r "row")))) ctx)) registered entries)
         ctx (if inactive (assoc ctx :explicit true) (sync/active ctx))
         by-label (into {} (for [r entries] [(get r "label") (hm (get-in r ["row" "name"]))]))]
     {:ctx ctx :rows (into {} (map (fn [r] [(get r "label") (get r "row")]) entries))
      :headers by-label :policy (apply j/level-instantiation-policy ctx (map by-label roles))})))
(defn engine [{:keys [ctx policy]}]
  (let [e (j/machine ctx)] (j/configure-level-instantiation! ctx e policy) e))
(defn call [ctx e label args] (j/start! ctx e label args) (sync/finish! ctx e))
(defn fields [ctx value] (mapv identity (.get ^java.lang.reflect.Field (:fields ctx) value)))
(defn retain [ctx e value] (j/retain! ctx e value) value)
(defn name! [ctx e s] (call ctx e "Lean.Name.str._override" [0 s]))
(defn mvar! [ctx e n] (call ctx e "Lean.Level.mvar._override" [n]))
(defn succ! [ctx e v] (call ctx e "Lean.Level.succ._override" [v]))
(defn fresh! [ctx e]
  (call ctx e "model-fresh-mctx" [(call ctx e "Lean.instInhabitedMetavarContext" [])]))
(defn assign! [ctx e m n value] (call ctx e "Lean.assignLevelMVarExp" [m n value]))
(defn instantiate! [ctx e m level] (call ctx e "Lean.instantiateLevelMVarsImp" [m level]))
(defn finish-pair! [ctx e pair] (sync/release! ctx e pair) (sync/close! ctx e))
(deftest authentic-fixture-and-owned-abi
  (let [rs (records) native (first (filter #(= "Lean.instantiateLevelMVarsImp" (get % "label")) rs))
        d (get-in native ["row" "ir" "extern"])]
    (is (= 66 (count rs)))
    (is (= "43de9c312f7e7a4bdeb9cd3b070ca4bd245fcca722f532b05f9e3083c1847605" (get native "sha256")))
    (is (= ["object" "tobject"] (mapv #(get % "ty") (get d "xs"))))
    (is (= [false false] (mapv #(get % "borrow") (get d "xs"))))))
(deftest carrier-fast-path-is-identity-and-does-not-demand-helper-bodies
  (let [{:keys [ctx] :as lab} (context {:defer roles}) e (engine lab)
        pair (instantiate! ctx e 0 0)]
    (is (= [0 0] (fields ctx pair))) (is (= "idle" (j/phase ctx e)))
    (finish-pair! ctx e pair)))
(deftest configuration-is-mandatory-once-idle-and-active-only
  (let [{:keys [ctx policy]} (context) e (j/machine ctx)]
    (is (g/bad? #(j/start! ctx e "Lean.instantiateLevelMVarsImp" [0 0])))
    (is (= "idle" (j/phase ctx e)))
    (j/configure-level-instantiation! ctx e policy)
    (is (g/bad? #(j/configure-level-instantiation! ctx e policy)))
    (sync/close! ctx e))
  (let [{:keys [ctx policy]} (context {:inactive true}) e (j/machine ctx)]
    (is (g/bad? #(j/configure-level-instantiation! ctx e policy))) (j/close! ctx e)))
(deftest unassigned-variable-preserves-exact-level-and-context
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
        level (mvar! ctx e (name! ctx e "unassigned")) pair (instantiate! ctx e m level)]
    (is (identical? m (first (fields ctx pair))))
    (is (identical? level (second (fields ctx pair))))
    (is (= 1 (c/rc ctx m) (c/rc ctx level)))
    (finish-pair! ctx e pair)))
(deftest closed-assignment-and-composite-reconstruction-use-original-constructors
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
        n (name! ctx e "assigned") level (mvar! ctx e (retain ctx e n))
        one (succ! ctx e 0) m (assign! ctx e m n (retain ctx e one))
        input (succ! ctx e level) pair (instantiate! ctx e m input)
        [out result] (fields ctx pair)]
    (is (identical? m out)) (is (not (identical? input result)))
    (is (= [one] (fields ctx result)))
    (is (true? (h/private-value input "dead")))
    (is (= 3 (c/rc ctx one)))
    (sync/release! ctx e one) (finish-pair! ctx e pair)))
(deftest assignment-chain-is-compressed-without-changing-an-outside-context
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
        a (name! ctx e "a") b (name! ctx e "b") c-name (name! ctx e "c")
        av (mvar! ctx e (retain ctx e a)) bv (mvar! ctx e (retain ctx e b)) cv (mvar! ctx e (retain ctx e c-name))
        one (succ! ctx e 0)
        m (assign! ctx e m c-name (retain ctx e one))
        m (assign! ctx e m b cv) m (assign! ctx e m (retain ctx e a) bv)
        outside (retain ctx e m) pair (instantiate! ctx e m av) [out result] (fields ctx pair)]
    (is (identical? one result)) (is (not (identical? outside out)))
    (let [old (call ctx e "Lean.getLevelMVarAssignmentExp" [(retain ctx e outside) (retain ctx e a)])
          current (call ctx e "Lean.getLevelMVarAssignmentExp" [(retain ctx e out) a])]
      (is (identical? bv (first (fields ctx old))))
      (is (identical? one (first (fields ctx current))))
      (sync/release! ctx e old) (sync/release! ctx e current))
    (sync/release! ctx e outside) (sync/release! ctx e one) (finish-pair! ctx e pair)))
(defn state [e]
  (loop [a (sync/action e)]
    (when a (or (h/private-value a "levelMvars") (recur (h/private-value a "parent"))))))
(defn materialize [{:keys [ctx headers rows]} label]
  (let [row (rows label) by-name (into {} (map (fn [[label h]] [(get-in (rows label) ["name"]) h]) headers))]
    (j/materialize-body ctx (headers label) row (mapv by-name (find/direct row)))))
(deftest getter-code-request-fork-owns-packet-exactly-once
  (let [label (first roles) {:keys [ctx headers] :as lab} (context {:defer #{label}})
        parent (engine lab) m (fresh! ctx parent) level (mvar! ctx parent (name! ctx parent "pause"))]
    (j/start! ctx parent "Lean.instantiateLevelMVarsImp" [m level])
    (let [request (code/request! ctx parent) packet (h/private-value (state parent) "call")
          {:keys [engine roots]} (j/fork! ctx parent [m level]) child engine [cm cl] roots
          ready (materialize lab label)]
      (is (identical? (headers label) (.header request)))
      (is (true? (h/private-value packet "entered")))
      (is (= [false false] (vec (h/private-value packet "owned"))))
      (is (= 2 (c/rc ctx m) (c/rc ctx cm)))
      (is (not (identical? packet (h/private-value (state child) "call"))))
      (doseq [[e expected-m expected-l] [[parent m level] [child cm cl]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [pair (sync/finish! ready e)]
          (is (identical? expected-m (first (fields ready pair))))
          (is (identical? expected-l (second (fields ready pair))))
          (is (= 1 (c/rc ready expected-m) (c/rc ready expected-l)))
          (finish-pair! ready e pair))))))
(deftest invalid-getter-result-stays-in-owned-receiver
  ;; Deliberately replaces an authenticated-shaped role BODY in this model source.
  ;; It tests protocol failure escrow, not authentic producer source admission.
  (let [body ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false
                    (c/let-ir 4 "object" (c/lit 0)
                      (c/let-ir 3 "object" (c/ctor 2 [(c/v 4)] 0) (c/ret 3)))]]
        {:keys [ctx] :as lab} (context {:replacements {(first roles) body}}) e (engine lab)
        m (fresh! ctx e) level (mvar! ctx e (name! ctx e "invalid"))]
    (j/start! ctx e "Lean.instantiateLevelMVarsImp" [m level])
    (is (re-find #"malformed Option" (c/failure #(sync/finish! ctx e))))
    (let [a (sync/action e) slot (h/private-value a "slot")
          receiver (aget ^objects (h/private-value e "objects") slot)]
      (is (= 2 (.getInt ^java.lang.reflect.Field (:tag ctx) receiver)))
      (is (= 1 (c/rc ctx receiver)))
      (is (some? (h/private-value (state e) "call")))
      (is (= 1 (c/rc ctx m) (c/rc ctx level))))))
(deftest constructor-code-request-and-fork-preserve-child-aliases
  (let [label (nth roles 2) {:keys [ctx headers] :as lab} (context {:defer #{label}})
        parent (engine lab) m (fresh! ctx parent) n (name! ctx parent "ctor-pause")
        variable (mvar! ctx parent (retain ctx parent n))
        input (call ctx parent (str "model-setup-" label) [variable])
        m (assign! ctx parent m n 0)]
    (j/start! ctx parent "Lean.instantiateLevelMVarsImp" [m input])
    (let [request (code/request! ctx parent) packet (h/private-value (state parent) "call")
          {:keys [engine roots]} (j/fork! ctx parent [m input]) child engine [cm ci] roots
          ready (materialize lab label)]
      (is (identical? (headers label) (.header request)))
      (is (= 2 (h/private-value packet "role")))
      (is (true? (h/private-value packet "entered")))
      (is (= [false] (vec (h/private-value packet "owned"))))
      (doseq [[e expected-m expected-input] [[parent m input] [child cm ci]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [pair (sync/finish! ready e) [out level] (fields ready pair)]
          (is (identical? expected-m out)) (is (= [0] (fields ready level)))
          (is (true? (h/private-value expected-input "dead")))
          (finish-pair! ready e pair))))))
(deftest setter-code-request-fork-has-stolen-context-and-retained-result
  (let [label (second roles) {:keys [ctx headers] :as lab} (context {:defer #{label}})
        parent (engine lab) m (fresh! ctx parent)
        a (name! ctx parent "set-a") b (name! ctx parent "set-b")
        av (mvar! ctx parent (retain ctx parent a)) bv (mvar! ctx parent (retain ctx parent b))
        m (call ctx parent (str "model-setup-" label) [m b 0])
        m (call ctx parent (str "model-setup-" label) [m a bv])]
    (j/start! ctx parent "Lean.instantiateLevelMVarsImp" [m av])
    (let [request (code/request! ctx parent) packet (h/private-value (state parent) "call")
          {:keys [engine roots]} (j/fork! ctx parent [m av]) child engine [cm ca] roots
          ready (materialize lab label)]
      (is (identical? (headers label) (.header request)))
      (is (= 1 (h/private-value packet "role")))
      (is (nil? (h/private-value (state parent) "context")))
      (is (= [false false false] (vec (h/private-value packet "owned"))))
      (doseq [[e expected-m root] [[parent m av] [child cm ca]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [pair (sync/finish! ready e)]
          (is (identical? expected-m (first (fields ready pair))))
          (is (= 0 (second (fields ready pair))))
          (is (true? (h/private-value root "dead")))
          (finish-pair! ready e pair))))))
(deftest smart-max-imax-run-only-after-an-actual-child-change
  (doseq [[operation side assignment expected] [["max" :left 0 :other] ["max" :right 0 :other]
                                                ["imax" :left 0 :other] ["imax" :right 0 :zero]
                                                ["max" :left :one :other] ["imax" :left :one :other]]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
          n (name! ctx e (str operation side assignment)) variable (mvar! ctx e (retain ctx e n))
          other (succ! ctx e (succ! ctx e 0))
          input (call ctx e (str "Lean.Level." operation "._override")
                      (if (= side :left) [variable (retain ctx e other)] [(retain ctx e other) variable]))
          value (if (= assignment :one) (succ! ctx e 0) 0)
          m (assign! ctx e m n value) pair (instantiate! ctx e m input) result (second (fields ctx pair))]
      (if (= expected :zero) (is (= 0 result)) (is (identical? other result)))
      (is (true? (h/private-value input "dead")))
      (sync/release! ctx e other) (finish-pair! ctx e pair)))
  (doseq [operation ["max" "imax"]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
          variable (mvar! ctx e (name! ctx e "unassigned-raw"))
          input (call ctx e (str "Lean.Level." operation "._override") [0 variable])
          pair (instantiate! ctx e m input)]
      ;; Zero-child normalization is deliberately NOT applied to unchanged nodes.
      (is (identical? input (second (fields ctx pair))))
      (finish-pair! ctx e pair))))
(deftest pre-entry-and-post-frame-tick-failure-distinguish-packet-owners
  (doseq [[field value entered] [["continuationDepth" (int 65536) false] ["callsLeft" (long 0) true]]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
          level (mvar! ctx e (name! ctx e "entry-failure"))]
      (j/start! ctx e "Lean.instantiateLevelMVarsImp" [m level])
      (sync/private-set! e field value)
      (is (g/bad? #(j/advance! ctx e 1)))
      (let [packet (h/private-value (state e) "call")]
        (is (= entered (h/private-value packet "entered")))
        (is (= [(not entered) (not entered)] (vec (h/private-value packet "owned"))))
        (is (= 2 (c/rc ctx m))) (is (= 1 (c/rc ctx level)))))))
(deftest encountered-assignment-cycle-and-work-budget-are-terminal-bounded-failures
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
        n (name! ctx e "cycle") variable (mvar! ctx e (retain ctx e n))
        m (assign! ctx e m n (retain ctx e variable))]
    (j/start! ctx e "Lean.instantiateLevelMVarsImp" [m variable])
    (is (re-find #"cycle outside profile" (c/failure #(sync/finish! ctx e))))
    (is (= "failed" (j/phase ctx e)))
    (is (= 1 (c/rc ctx m))) (is (= 4 (c/rc ctx variable))))
  (let [{:keys [ctx] :as lab} (context) e (engine lab)]
    (j/start! ctx e "Lean.instantiateLevelMVarsImp" [0 0])
    ;; Model resource exhaustion injects the already-consumed aggregate budget.
    (sync/private-set! (state e) "work" (long 1000000))
    (is (re-find #"work outside bounded" (c/failure #(sync/finish! ctx e))))
    (is (= "failed" (j/phase ctx e)))))
(deftest cache-is-shared-composite-only-including-logical-mt
  (doseq [mode [:unique :shared :mt :mt-mvar]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
          variable (mvar! ctx e (name! ctx e (str mode)))
          input (if (= mode :mt-mvar) variable (succ! ctx e variable))]
      (when (= mode :shared) (retain ctx e input))
      (when (#{:mt :mt-mvar} mode) (sharing/mark! ctx e input))
      (j/start! ctx e "Lean.instantiateLevelMVarsImp" [m input])
      (loop [left 10000]
        (assert (pos? left) "No bounded traversal result")
        (when-not (= 1 (h/private-value (state e) "stage"))
          (is (false? (j/advance! ctx e 1))) (recur (dec left))))
      (let [cache (h/private-value (state e) "cache")]
        (is (= (if (#{:shared :mt} mode) 1 0) (.size ^java.util.Map cache)))
        (when (#{:shared :mt} mode) (is (.containsKey ^java.util.Map cache input))))
      (let [pair (sync/finish! ctx e)]
        (is (identical? input (second (fields ctx pair))))
        (when (= mode :shared) (sync/release! ctx e input))
        (finish-pair! ctx e pair)))))
(deftest owned-boxed-pap-ap-and-inactive-preclaim
  (let [{:keys [ctx] :as lab} (context) e (engine lab)
        pair (call ctx e "Lean.instantiateLevelMVarsImp._boxed" [0 0])]
    (is (= [0 0] (fields ctx pair))) (sync/release! ctx e pair)
    (let [closure (j/make-closure! ctx e "Lean.instantiateLevelMVarsImp" [0])
          row (c/decl "model-apply-level" [(c/p 1 "object") (c/p 2 "object")] "object"
                (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
          ready (j/extend-program ctx (x/raw [row]))]
      (j/install-program! ready e)
      (let [pair (call ready e "model-apply-level" [closure 0])]
        (is (= [0 0] (fields ready pair)))
        (is (true? (h/private-value closure "dead")))
        (sync/release! ready e pair))
      (sync/close! ready e)))
  (let [{:keys [ctx]} (context {:inactive true})
        row (c/decl "model-inactive-apply-level" [(c/p 1 "object") (c/p 2 "object")] "object"
              (c/let-ir 3 "object" {:ap {:x {:idx 1} :ys [(c/v 2)]}} (c/ret 3)))
        ctx (j/extend-program ctx (x/raw [row])) e (j/machine ctx)
        closure (j/make-closure! ctx e "Lean.instantiateLevelMVarsImp" [0])]
    (is (g/bad? #(j/start! ctx e "Lean.instantiateLevelMVarsImp" [0 0])))
    (is (= "idle" (j/phase ctx e))) (is (= 1 (c/rc ctx closure)))
    (j/start! ctx e "model-inactive-apply-level" [closure 0])
    (is (g/bad? #(sync/finish! ctx e)))
    (is (= 1 (c/rc ctx closure))) (is (false? (h/private-value closure "dead")))
    (is (= "failed" (j/phase ctx e))) (is (g/bad? #(j/close! ctx e)))))
(deftest getter-claimed-host-cleanup-demands-code-host-and-forks
  ;; Controlled getter BODY model exercises real Promise release control, not the
  ;; authenticated source getter algorithm. All task rows themselves are original.
  (let [consume (h/spec "research_level_consume_promise" ["object"] [true] "object")
        event (h/spec "research_level_drop_event" ["object"] [true] "object")
        finalizer (c/decl "model-level-finalizer" [(c/p 1 "object")] "object"
                    (c/let-ir 2 "object" (c/fap "model-level-drop-event" [(c/v 1)])
                      ["dec" {:idx 1} 1 false false (c/ret 2)]))
        body (c/let-ir 10 "object" (c/lit 1)
               (c/let-ir 3 "object" (sync/sfap "IO.Promise.new._boxed" ["erased" "erased" "erased"])
                 ["inc" {:idx 3} 1 false false
                  (c/let-ir 4 "object" (sync/sfap "IO.Promise.result?._boxed" ["erased" (c/v 3)])
                    (c/let-ir 5 "object" {:pap {:c (c/name-ir "model-level-finalizer") :ys []}}
                      (c/let-ir 6 "object" (sync/sfap "Task.map._boxed" ["erased" "erased" (c/v 5) (c/v 4) "erased" (c/v 10)])
                        (c/let-ir 7 "object" {:pap {:c (c/name-ir "model-level-consume-promise") :ys []}}
                          (c/let-ir 8 "object" {:ap {:x {:idx 7} :ys [(c/v 3)]}}
                            ["dec" {:idx 6} 1 false false
                             ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false
                              (c/let-ir 9 "tobject" (c/lit 0) (c/ret 9))]]])))))]))
        {:keys [ctx headers] :as lab}
        (context {:tasks true :host-specs [consume event] :defer #{"model-level-finalizer"}
                  :replacements {(first roles) body}
                  :rows [(h/ext "model-level-consume-promise" consume)
                         (h/ext "model-level-drop-event" event) finalizer]})
        parent (engine lab) m (fresh! ctx parent) input (mvar! ctx parent (name! ctx parent "host-cleanup"))]
    (j/start! ctx parent "Lean.instantiateLevelMVarsImp" [m input])
    (let [r (h/request! ctx parent) promise (first (h/args r))]
      (is (= "research_level_consume_promise" (j/request-value r "symbol")))
      (j/resume-host! ctx parent r 0)
      (let [request (code/request! ctx parent)
            {:keys [engine roots]} (j/fork! ctx parent [m input promise]) child engine [cm ci cp] roots
            ready (materialize lab "model-level-finalizer")]
        (is (identical? (headers "model-level-finalizer") (.header request)))
        (is (true? (h/private-value (h/private-value parent "hostCompletion") "replyClaimed")))
        (doseq [[e em ei ep] [[parent m input promise] [child cm ci cp]]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [r (h/request! ready e)]
            (is (= "research_level_drop_event" (j/request-value r "symbol")))
            (is (= [0] (h/args r))) (j/resume-host! ready e r 0))
          (let [pair (sync/finish! ready e)]
            (is (identical? em (first (fields ready pair))))
            (is (identical? ei (second (fields ready pair))))
            (is (true? (h/private-value ep "dead")))
            (is (nil? (state e))) (is (nil? (h/private-value e "hostCompletion")))
            (finish-pair! ready e pair)))))))
(deftest raw-max-and-imax-helpers-suspend-fork-and-preserve-original-cached-data
  (doseq [operation ["max" "imax"]]
    (let [label (str "Lean.Level." operation "._override")
          {:keys [ctx headers] :as lab} (context {:defer #{label}}) parent (engine lab)
          m (fresh! ctx parent) n (name! ctx parent "raw-assigned")
          variable (mvar! ctx parent (retain ctx parent n))
          p (call ctx parent "Lean.Level.param._override" [(name! ctx parent "p")])
          q (call ctx parent "Lean.Level.param._override" [(name! ctx parent "q")])
          expected (call ctx parent (str "model-setup-" label) [(retain ctx parent p) (retain ctx parent q)])
          input (call ctx parent (str "model-setup-" label) [variable (retain ctx parent q)])
          m (assign! ctx parent m n (retain ctx parent p))]
      (j/start! ctx parent "Lean.instantiateLevelMVarsImp" [m input])
      (let [request (code/request! ctx parent)
            {:keys [engine roots]} (j/fork! ctx parent [p q expected]) child engine [cp cq ce] roots
            ready (materialize lab label)]
        (is (identical? (headers label) (.header request)))
        (doseq [[e ep eq expected-node] [[parent p q expected] [child cp cq ce]]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [pair (sync/finish! ready e) result (second (fields ready pair))]
            (is (every? true? (map identical? [ep eq] (fields ready result))))
            (is (= (vec (.get ^java.lang.reflect.Field (:scalars ready) expected-node))
                   (vec (.get ^java.lang.reflect.Field (:scalars ready) result))))
            (doseq [value [ep eq expected-node]] (sync/release! ready e value))
            (finish-pair! ready e pair)))))))
(deftest smart-absorption-equal-levels-and-same-base-successor-offset
  (doseq [mode [:equal :absorb :offset]]
    (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
          n (name! ctx e "smart-var") variable (mvar! ctx e (retain ctx e n))
          p (call ctx e "Lean.Level.param._override" [(name! ctx e "smart-p")])
          selected (case mode
                     :equal (retain ctx e p)
                     :absorb (call ctx e "Lean.Level.max._override"
                                   [(retain ctx e p) (call ctx e "Lean.Level.param._override" [(name! ctx e "smart-q")])])
                     :offset (succ! ctx e (succ! ctx e (retain ctx e p))))
          right (if (= mode :offset) (succ! ctx e variable) variable)
          input (call ctx e "Lean.Level.max._override" [(retain ctx e selected) right])
          m (assign! ctx e m n p) pair (instantiate! ctx e m input)]
      (is (identical? selected (second (fields ctx pair))))
      (sync/release! ctx e selected) (finish-pair! ctx e pair))))
(deftest repeated-shared-composite-hits-cache-and-reuses-owned-result
  (let [{:keys [ctx] :as lab} (context) e (engine lab) m (fresh! ctx e)
        n (name! ctx e "dag") variable (mvar! ctx e (retain ctx e n))
        shared (succ! ctx e variable) input (call ctx e "Lean.Level.max._override" [(retain ctx e shared) shared])
        m (assign! ctx e m n 0) hit (atom false)]
    (j/start! ctx e "Lean.instantiateLevelMVarsImp" [m input])
    (loop [left 10000]
      (assert (pos? left) "Shared DAG test exceeded bounded work")
      (let [s (state e) frame (.peekLast ^java.util.Deque (h/private-value s "frames"))]
        (when (and frame (identical? shared (h/private-value frame "original"))
                   (true? (h/private-value frame "cached")) (= 8 (h/private-value frame "stage")))
          (reset! hit true))
        (when-not (= 1 (h/private-value s "stage"))
          (j/advance! ctx e 1) (recur (dec left)))))
    (is @hit)
    (let [s (state e) values (h/private-value s "cacheValues")
          cached (h/private-value (.get ^java.util.List values 0) "value")]
      (is (= 1 (.size ^java.util.List values)))
      (let [pair (sync/finish! ctx e)]
        (is (identical? cached (second (fields ctx pair))))
        (is (= [0] (fields ctx cached)))
        (finish-pair! ctx e pair)))))
(deftest exact-role-source-and-raw-abi-policy-negatives-have-no-owner-effects
  (let [{:keys [ctx headers rows] :as lab} (context) e (engine lab)
        getter (first roles) hs (mapv headers roles)
        source (j/source-binding ctx (Object.))
        foreign (j/declaration-header source (rows getter)
                    "2be7a950bc5a94407c262d74d69b8381e3cb0f399ac04256e158fb53500f37ec")
        borrowed-row (assoc-in (rows getter) ["ir" "fdecl" "xs" 0 "borrow"] true)
        borrowed (j/declaration-header (.source (hs 0)) borrowed-row
                   "2be7a950bc5a94407c262d74d69b8381e3cb0f399ac04256e158fb53500f37ec")
        level (mvar! ctx e (name! ctx e "alias-input")) before (j/instructions ctx e)]
    (is (g/bad? #(apply j/level-instantiation-policy ctx (assoc hs 0 foreign))))
    (is (g/bad? #(apply j/level-instantiation-policy ctx (assoc hs 0 borrowed))))
    (is (g/bad? #(apply j/level-instantiation-policy ctx (assoc hs 0 (hs 1)))))
    (is (= before (j/instructions ctx e)))
    (is (g/bad? #(j/start! ctx e "Lean.instantiateLevelMVarsImp" [level level])))
    (is (= 1 (c/rc ctx level))) (is (= "idle" (j/phase ctx e)))
    (sync/release! ctx e level) (sync/close! ctx e)))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-level-mvars-checks)))
