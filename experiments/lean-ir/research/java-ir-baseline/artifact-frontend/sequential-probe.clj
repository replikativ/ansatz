(ns sequential-frontend-probe
  "Bounded sequential original-guest frontend probe; no frontend/kernel replacement.

  Requires an explicitly attached authenticated demand resolver.
  setup! BORROWS the real mkEmptyEnvironment Env payload; it never steals the
  caller's owner. Every :owners entry below represents exactly one host credit.
  Observations contain borrowed references tied to those retained owner entries.

  Pin:819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Source-verified layouts:
  Frontend.lean:21–31,67–88; Parser/Module.lean:75–112;
  Parser/Extension.lean:459–476; Elab/Command.lean:99–106;
  Elab/Import.lean:24–45. Exact original rows remain under the existing driver
  source binding; no synthesized fdecl is installed."
  (:require [clojure.data.json :as json] [clojure.string :as str]
            [java-ir-baseline :as j] [ansatz.research.ir.catalogue :as cat]
            [ansatz.research.ir.authenticated-demand :as demand]))
(def text "prelude\naxiom HostedSort : Sort 1\n")
(assert (= "b348ab678fc4d134aa75859764d0a4d40890f81e2d168f0f2ba2d9a997a1ae6b"
           (apply str (map #(format "%02x" (bit-and 255 %))
             (.digest (java.security.MessageDigest/getInstance "SHA-256")
                      (.getBytes ^String text java.nio.charset.StandardCharsets/UTF_8))))))
(def filename "sequential-probe.lean")
(defn host-helper [name]
  ;; Preserve the existing call facade while eliminating ambient user Vars.
  (case name
    "ensure-header!" demand/ensure-header!
    "service-code!" demand/service-code!
    "original-row!" demand/original-row!
    (throw (ex-info "Unknown authenticated demand helper" {:helper name}))))
(defn ctx [s] @(:current-ctx (:driver s)))
(defn engine [s] (:engine (:driver s)))
(defn owned [s key]
  (let [m @(:owners s)] (assert (contains? m key) (str "Missing owner: " key)) (get m key)))
(defn hold! [s key value]
  (assert (not (contains? @(:owners s) key)) (str "Duplicate owner: " key))
  (swap! (:owners s) assoc key value) value)
(defn take-owner! [s key]
  (let [value (owned s key)] (swap! (:owners s) dissoc key) value))
(defn retain-as! [s key value]
  (assert (not (contains? @(:owners s) key)))
  (j/retain! (ctx s) (engine s) value) (hold! s key value))
(defn facade-owner! [s key]
  (let [value (owned s key)] (j/retain! (ctx s) (engine s) value) value))
(defn fields [s value]
  (assert (.isInstance ^Class (:node-class (ctx s)) value) "Expected real engine Node")
  (.get ^java.lang.reflect.Field (:fields (ctx s)) value))
(defn scalars [s value] (.get ^java.lang.reflect.Field (:scalars (ctx s)) value))
(defn ctor! [s value tag n]
  (let [f (fields s value)]
    (assert (= tag (.getInt ^java.lang.reflect.Field (:tag (ctx s)) value)))
    (assert (= n (alength ^objects f))) f))
(defn phase-info [s]
  {:phase (j/phase (ctx s) (engine s))
   :active (j/active (ctx s) (engine s))
   :budget @(:used s) :in-flight @(:in-flight s)})
(defn check-time! [s]
  (when (> (System/nanoTime) (:deadline-nanos s))
    (throw (ex-info "60-second cooperative probe deadline reached" (phase-info s)))))
(defn charge! [s key amount]
  (let [n (get (swap! (:used s) update key (fnil + 0) amount) key)]
    (when (> n (get (:limits s) key))
      (throw (ex-info "Global sequential probe budget reached" (assoc (phase-info s) :limit key))))))
(defn drain! [s]
  (loop []
    (check-time! s)
    (let [driver (:driver s) c (ctx s) e (engine s) phase (j/phase c e)]
      (cond
        (= phase "complete") (j/take-result! c e)
        (= phase "code-call")
        (do (charge! s :turns 1) (charge! s :code-requests 1)
            ((host-helper "service-code!") driver) (recur))
        (= phase "running")
        (let [left (- (get-in s [:limits :instructions]) (:instructions @(:used s)))
              _ (when (<= left 0) (throw (ex-info "Global instruction bound reached" (phase-info s))))
              before (j/instructions c e)]
          (charge! s :turns 1)
          ;; instructionCount resets at each start, so accumulate deltas here
          ;; across ALL guest calls, releases, observations and command steps.
          (j/advance! c e (min 100 left))
          (charge! s :instructions (- (j/instructions (ctx s) e) before))
          (recur))
        (and (contains? #{"host-call" "host-guest-result"} phase) (:runtime-step! s))
        (do (charge! s :turns 1) ((:runtime-step! s) s) (recur))
        :else (throw (ex-info "Genuine guest/runtime boundary" (phase-info s)))))))
(defn typed-name [label]
  (reduce (fn [parent segment] ["str" parent segment]) ["anonymous"] (str/split label #"\.")))
(defn entry-label [s label]
  ;; All entries used here are accepted base declarations. Prefer actual boxed
  ;; ownership facades; never invent an absent wrapper or assume borrowed roots.
  (let [candidate (str label "._boxed")]
    (if (cat/lookup (get-in s [:driver :catalogue]) (typed-name candidate)) candidate label)))
(defn call! [s label args]
  (reset! (:in-flight s) {:operation :call :label label :arguments args :stage :not-started})
  (check-time! s)
  (let [driver (:driver s) label (entry-label s label)
        header ((host-helper "ensure-header!") driver (typed-name label))
        c (j/register-headers (ctx s) [header])]
    (j/install-program! c (engine s)) (reset! (:current-ctx driver) c)
    (reset! (:in-flight s) {:operation :call :label label :arguments args :stage :starting})
    (swap! (:calls s) conj {:label label :row-sha256 (j/request-value header "originalSha256")})
    (j/start! c (engine s) label args)
    (swap! (:in-flight s) assoc :stage :started)
    (let [value (drain! s)] (reset! (:in-flight s) nil) value)))
(defn release-value! [s value]
  (reset! (:in-flight s) {:operation :release :value value :stage :not-started})
  (check-time! s)
  (swap! (:in-flight s) assoc :stage :starting)
  (j/start-release! (ctx s) (engine s) value 1)
  (swap! (:in-flight s) assoc :stage :started)
  (let [result (drain! s)] (assert (= 0 result)) (reset! (:in-flight s) nil)))
(defn drop! [s key] (release-value! s (take-owner! s key)))
(defn take-ok! [s result-key payload-key]
  (let [result (owned s result-key) payload (aget ^objects (ctor! s result 0 1) 0)]
    (retain-as! s payload-key payload) (drop! s result-key) payload))
(defn bool! [value]
  (assert (or (= 0 value) (= 1 value)) "Expected actual Bool") (= 1 value))
(defn error-log? [s key]
  (bool! (call! s "Lean.MessageLog.hasErrors" [(facade-owner! s key)])))
(defn assemble-state! [s]
  ;; The sole reflective allocation is ordinary Frontend.State, not an opaque
  ;; kernel/environment value. Allocate BEFORE transferring donor credits.
  ;; It is excluded from the engine's allocations counter; adapter count is 1.
  (let [keys [:command-state :parser-state :command-pos :commands]
        _ (doseq [key keys] (owned s key))
        constructor (.getDeclaredConstructor ^Class (:node-class (ctx s))
                         (into-array Class [Integer/TYPE Integer/TYPE Integer/TYPE]))]
    (.setAccessible constructor true)
    (let [value (.newInstance constructor (object-array [(int 0) (int 4) (int 0)]))
          f (ctor! s value 0 4)]
      (assert (= 1 (.getInt ^java.lang.reflect.Field (:rc (ctx s)) value)))
      (assert (zero? (alength ^bytes (scalars s value))))
      (doseq [[i key] (map-indexed vector keys)] (aset ^objects f i (take-owner! s key)))
      (hold! s :frontend-state value))))
(defn snapshot! [s index]
  (let [state-key [:frontend-state index]
        state (hold! s state-key (call! s "ST.Prim.Ref.get" [0 0 (facade-owner! s :state-ref) 0]))
        sf (ctor! s state 0 4) command-state (aget ^objects sf 0)
        cf (ctor! s command-state 0 11) ps (aget ^objects sf 1)
        pf (ctor! s ps 0 1) flags (scalars s ps)
        message-key [:messages index]
        _ (assert (= 2 (alength ^bytes flags)))
        _ (assert (every? #{0 1} (map #(Byte/toUnsignedInt %) flags)))
        _ (retain-as! s message-key (aget ^objects cf 1))
        commands (aget ^objects sf 3)
        _ (j/retain! (ctx s) (engine s) commands)
        count (call! s "Array.size" [0 commands])
        _ (assert (and (integer? count) (<= 0 count 8)))
        syntax (when (pos? count) (aget ^objects (fields s commands) (dec count)))
        observation {:index index :has-errors (error-log? s message-key)
                     :parser-pos (aget ^objects pf 0) :recovering (Byte/toUnsignedInt (aget ^bytes flags 0))
                     :has-leading (Byte/toUnsignedInt (aget ^bytes flags 1))
                     :cmd-pos (aget ^objects sf 2) :command-count count
                     ;; Borrowed below, owned transitively by state-key. Do not
                     ;; DEC these aliases or keep them after releasing session.
                     :command-state command-state :environment (aget ^objects cf 0)
                     :messages (owned s message-key) :latest-syntax syntax
                     :state-owner-key state-key :messages-owner-key message-key
                     :budget @(:used s)}]
    (swap! (:observations s) conj observation) observation))
(defn failure [s error]
  (let [c (ctx s) e (engine s)
        request (try (j/code-request c e) (catch Throwable _ nil))
        header (when request (j/request-value request "header"))]
    {:status :boundary :session s :boundary (phase-info s) :error error
     :failure-causes (mapv (fn [^Throwable cause] {:type (.getName (class cause)) :message (.getMessage cause)
                                                   :data (when (instance? clojure.lang.IExceptionInfo cause) (ex-data cause))})
                          (take-while some? (iterate (fn [^Throwable cause] (.getCause cause)) error)))
     :failed-code-request (when header {:request request :name (j/lean-name-data (j/request-value header "name"))
                                       :sha256 (j/request-value header "originalSha256")
                                       :kind (j/request-value header "kind")})
     :checked-declaration-established false}))
(defn preflight-real-env! [s value]
  ;; Marshalling guard only, not provenance/nominal-type authentication.
  ;; Pinned mkEmptyEnvironment original row2b8f1995... and setMainModule
  ;; row66757ae6... both construct Lean.Environment tag0/8 owning fields/1
  ;; Bool byte. The outer EST.Out.ok IO result is tag0/1 field/0 bytes.
  (let [c (ctx s) node? (.isInstance ^Class (:node-class c) value)
        shape (when node? {:tag (.getInt ^java.lang.reflect.Field (:tag c) value)
                           :fields (alength ^objects (fields s value))
                           :scalar-bytes (alength ^bytes (scalars s value))})]
    (when-not (and (= {:tag 0 :fields 8 :scalar-bytes 1} shape)
                   (contains? #{0 1} (Byte/toUnsignedInt (aget ^bytes (scalars s value) 0))))
      (throw (ex-info "Expected borrowed Lean.Environment payload: tag0/8fields/1Bool byte; unwrap actual IO.Result first and preserve its owner"
                      {:received shape :guest-call-started false :guest-owner-acquired false})))
    value))
(defn setup! [driver real-env]
  (let [s {:driver driver :owners (atom {}) :observations (atom []) :calls (atom []) :in-flight (atom nil)
           :deadline-nanos (+ (System/nanoTime) 60000000000)
           :limits {:instructions 3000000 :code-requests 3000 :turns 50000 :commands 3}
           :used (atom {:instructions 0 :code-requests 0 :turns 0 :commands 0})}]
    (try
      ;; FIRST check: no guest call, retain or reflective allocation before this.
      (preflight-real-env! s real-env)
      (assert (= "idle" (j/phase (ctx s) (engine s))))
      (assert (:task-runtime (ctx s)) "Require explicit active synchronous runtime")
      (let [size (call! s "String.utf8ByteSize" [text])
            input (hold! s :input (call! s "Lean.Parser.mkInputContext._redArg" [text filename 1 size]))]
        (ctor! s input 0 4)
        (hold! s :header-result (call! s "Lean.Parser.parseHeader" [(facade-owner! s :input) 0]))
        (let [payload (aget ^objects (ctor! s (owned s :header-result) 0 1) 0)
              pair (ctor! s payload 0 2) rest (ctor! s (aget ^objects pair 1) 0 2)]
          (retain-as! s :header (aget ^objects pair 0))
          (retain-as! s :parser-state (aget ^objects rest 0))
          (retain-as! s :header-messages (aget ^objects rest 1)))
        (drop! s :header-result)
        (retain-as! s :header-messages-observation (owned s :header-messages))
        (assert (not (error-log? s :header-messages)) "Header diagnostics reported errors")
        (assert (not (bool! (call! s "Lean.Elab.HeaderSyntax.isModule" [(facade-owner! s :header)]))) "Module file outside fixed probe")
        (hold! s :prelude-stx (call! s "Lean.Syntax.getArg" [(facade-owner! s :header) 1]))
        (assert (not (bool! (call! s "Lean.Syntax.isNone" [(take-owner! s :prelude-stx)]))) "Actual prelude required")
        (hold! s :imports (call! s "Lean.Elab.HeaderSyntax.imports" [(facade-owner! s :header) 1]))
        (assert (= 0 (call! s "Array.size" [0 (take-owner! s :imports)])) "Imports/implicit Init outside fixed probe")
        (drop! s :header)
        (let [module-name (call! s "Lean.Name.mkStr2" ["Hosted" "SequentialProbe"])]
          (j/retain! (ctx s) (engine s) real-env)
          (hold! s :environment (call! s "Lean.Environment.setMainModule" [real-env module-name])))
        (hold! s :options (call! s "Lean.Options.empty" []))
        (doseq [[prefix leaf] (concat [["Elab" "async"] ["debug" "skipKernelTC"]]
                                      (get (ctx s) :lab-false-bool-options []))]
          (let [name (call! s "Lean.Name.mkStr2" [prefix leaf])]
            (hold! s :options (call! s "Lean.Options.setBool" [(take-owner! s :options) name 0]))))
        ;; Strict native-kernel prototype: disable the TWO original native
        ;; resource limits through real guest options. VM/projection/checker
        ;; host budgets remain separately enforced and are not native counters.
        (doseq [option ["maxHeartbeats" "maxRecDepth"]]
          (let [name (call! s "Lean.Name.mkStr1" [option])
                nat-value-instance (call! s "Lean.KVMap.instValueNat" [])]
            (hold! s :options (call! s "Lean.Options.set" [0 nat-value-instance (take-owner! s :options) name 0]))))
        (hold! s :command-state (call! s "Lean.Elab.Command.mkState"
                                  [(take-owner! s :environment) (take-owner! s :header-messages) (take-owner! s :options)]))
        (let [ps (owned s :parser-state) f (ctor! s ps 0 1)]
          (assert (= 2 (alength ^bytes (scalars s ps))))
          (retain-as! s :command-pos (aget ^objects f 0)))
        (hold! s :commands (call! s "Array.emptyWithCapacity" [0 0]))
        (assemble-state! s)
        (hold! s :state-ref (call! s "ST.Prim.mkRef" [0 0 (take-owner! s :frontend-state) 0]))
        {:status :prepared :session s :initial-observation (snapshot! s 0)
         :adapter-allocations 1 :checked-declaration-established false})
      (catch Throwable error
        (failure s error)))))
(defn step! [s]
  (try
    (charge! s :commands 1)
    (let [index (:commands @(:used s))
          result-key [:process-result index]
          _ (hold! s result-key (call! s "Lean.Elab.Frontend.processCommand"
                                     [(facade-owner! s :input) (facade-owner! s :state-ref) 0]))
          done (aget ^objects (ctor! s (owned s result-key) 0 1) 0)]
      (assert (or (= 0 done) (= 1 done)))
      (drop! s result-key)
      {:status :command-observed :done (bool! done) :session s :observation (snapshot! s index)
       :checked-declaration-established false})
    (catch Throwable error
      (failure s error))))
(defn release-session! [s]
  ;; Call ONLY while idle after all results were taken. This does NOT dispose
  ;; the shared driver, caller's original env, catalogue, or captured companion.
  ;; Releasing states may run genuine finalizers via the same bounded driver.
  (doseq [key (vec (keys @(:owners s)))] (drop! s key))
  {:status :session-owners-released :budget @(:used s)})

;; RETAINED REPL, from experiments/lean-ir; no JVM launch:
;; Pass the Env PAYLOAD, not mkEmptyEnvironment's outer IO.Result/EST.Out.ok.
;; If sync-env-io is the caller-owned real successful IO result:
;;   payload = field0 of that verified tag0/1field/0scalar wrapper.
;; Keep the wrapper owner LIVE across setup! (which retains its own payload copy),
;; or explicitly retain payload before releasing wrapper via active release.
;; (def sequential (sequential-frontend-probe/setup! sync-driver sync-env-payload))
;; Require :prepared, inspect :initial-observation, then:
;; (def sequential-axiom (sequential-frontend-probe/step! (:session sequential)))
;; Inspect this observation BEFORE EOF. Never infer checked kernel admission
;; from no errors or env presence; actual lean_elab_add_decl boundary may stop.
;; Optional next (separate receipt) step processes EOF. Retain prior observations.
;; Release with release-session! only when idle/complete results were taken.
;; On boundary/budget/failure preserve :session and :in-flight, do not auto-release
;; unknown claimed call arguments or fabricate continuation success.

;; Hazards: budget deadline is cooperative at helper/advance boundaries, not a
;; thread interrupter. It starts at setup!, spans later step!/release calls, and
;; is not silently reset between commands. A parent may explicitly assoc a new
;; :deadline-nanos after inspecting a recorded stop, without restarting claims.
;; Each snapshot keeps a Frontend.State owner plus a separate MessageLog owner.
;; Do not use observations after release-session!. No earlier parser diagnostics
;; preservation claim: original top-level elaboration resets messages; PLAN.md
;; explains the limitation. A no-error observation is not kernel admission.
;; Existing source-call! signature is [driver label arguments], user namespace;
;; this helper uses ensure-header! [driver name] and service-code! [driver] from
;; the same user namespace, with its own globally bounded driver loop instead.
