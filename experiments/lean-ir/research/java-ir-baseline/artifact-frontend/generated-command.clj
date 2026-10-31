(ns generated-command-receipt-v1
  "Trusted research controller. Never seals a pre-existing diagnostic observation.
   SourceCaptures are trusted driver code, not validation of caller Boolean maps."
  (:refer-clojure :exclude [run!])
  (:require [clojure.data.json :as json] [clojure.set :as set]
            [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [ansatz.research.ir.catalogue :as cat]
            [ansatz.research.ir.node-decoder-v1 :as decoder]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [artifact-declaration-authority-v4 :as authority])
  (:import [java.util WeakHashMap LinkedHashMap] [ansatz.kernel ConstantInfo Expr Name]))
(deftype SourceCaptures [])
(deftype CommandRun [])
(deftype CodeBatch [])
(defonce ^:private providers (WeakHashMap.))
(defonce ^:private runs (WeakHashMap.))
(defonce ^:private batches (WeakHashMap.))
(defonce ^:private busy-engines (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:scope :generated-command-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- get-issued [registry token]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info "Actual issued token required" {})))))
(defn- put-issued [registry token value] (locking registry (.put ^WeakHashMap registry token value)) token)
(defn source-captures
  "TRUSTED HOST constructor. Hooks must inspect actual source/layout/options and
   compilation callback lineage; this factory does not authenticate hook code.
   :before-command! returns actual input/state/options witness plus owner-free
   :description; :check! revokes its live source lease. Hooks cannot advance VM.
   :before-call! and :after-taken! observe actual staged call/result identities."
  [{:keys [check! before-command! before-call! after-taken! inspect-observation!] :as hooks}]
  (doseq [f [check! before-command! before-call! after-taken! inspect-observation!]] (need (fn? f) "Complete independent SourceCaptures required"))
  (put-issued providers (SourceCaptures.) hooks))
(defn- state [run] @(get-issued runs run))
(defn- ctx [s] @(:current-ctx (:driver (:frontend s))))
(defn- engine [s] (:engine (:driver (:frontend s))))
(defn- hook-stamp [e]
  {:counts (mapv #(field e %) ["instructions" "allocations" "stores" "retains" "releases" "shellDeletes"])
   :identities (mapv #(field e %) ["program" "pc" "entry" "hostRequest" "codeRequest" "runtimeAction"])
   :flags (mapv #(field e %) ["closed" "disposed" "untrackedFailure" "advancing"])})
(defn- observe! [holder key argument]
  (let [s @holder e (engine s) before (hook-stamp e) result ((get-in s [:hooks key]) argument)
        after (hook-stamp e)]
    (need (and (= (:counts before) (:counts after)) (= (:flags before) (:flags after))
               (every? true? (map identical? (:identities before) (:identities after))))
          "Source observer advanced or mutated engine custody") result))
(defn- live! [holder]
  (let [s @holder]
    (need (not (contains? #{:failed :retired} (:status s))) "Command controller is terminal")
    (need (identical? (:thread s) (Thread/currentThread)) "Command controller is thread confined")
    (let [e (engine s) c (ctx s) session (:adapter (:strict-driver s))]
    (need (and (identical? e (:engine session)) (identical? (:class c) (class e))
               (identical? (:program c) (field e "program"))
               (identical? (:source s) (:source session))) "Actual engine/Program/source session differs")
    (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]] (need (false? (field e k)) "Engine lifecycle prevents compilation custody"))
    ((get-in s [:strict-driver :authority :check-source!]) e (:source s))
    (observe! holder :check! {:engine e :source (:source s) :frontend (:frontend s)})
    s)))
(defn- new-slot! [holder key]
  (let [slot (object-array [nil :pending]) owners ^LinkedHashMap (:owners @holder)]
    (need (nil? (.putIfAbsent owners key slot)) "Duplicate command owner key") slot))
(defn- owned [holder key]
  (let [slot (.get ^LinkedHashMap (:owners @holder) key)]
    (need (and slot (= :owned (aget ^objects slot 1))) "Command occurrence is not owned") (aget ^objects slot 0)))
(defn- retain! [holder key value]
  (let [slot (new-slot! holder key) s (live! holder)]
    (aset ^objects slot 0 value)
    (aset ^objects slot 1 :retain-pending)
    (j/retain! (ctx s) (engine s) value)
    (aset ^objects slot 1 :owned) value))
(defn- exact-header! [s header]
  (let [c (ctx s) source (:source s) p (:program c)]
    (need (and header (identical? source (j/request-value header "source"))) "Call Header has another SourceBinding")
    (.invoke (.getMethod (class p) "functionId" (into-array Class [(class header)])) p (object-array [header]))
    header))
(defn- entry-header [e] (when-let [entry (field e "entry")] (field entry "header")))
(defn- entry-live! [s operation]
  (when (= :call (:kind operation))
    (need (identical? (:header operation) (entry-header (engine s))) "Root entry differs from staged actual Header")))
(defn- drain! [holder result-slot]
  (loop []
    (let [s (live! holder) f (:frontend s) c (ctx s) e (engine s) op (:operation s) phase (j/phase c e)]
      (sp/check-time! f) (entry-live! s op)
      (cond
        (= phase "complete")
        (do
          ;; Exact root Header was rechecked above, before the actual owned take.
          (aset ^objects result-slot 1 :take-pending)
          (j/take-result! c e))
        (= phase "code-call")
        (do (sp/charge! f :turns 1) (sp/charge! f :code-requests 1)
            ((sp/host-helper "service-code!") (:driver f)) (recur))
        (= phase "running")
        (let [left (- (get-in f [:limits :instructions]) (:instructions @(:used f))) before (j/instructions c e)]
          (need (pos? left) "Command instruction budget exhausted") (sp/charge! f :turns 1)
          (j/advance! c e (min 100 left))
          (sp/charge! f :instructions (- (j/instructions (ctx @holder) e) before)) (recur))
        (and (contains? #{"host-call" "host-guest-result"} phase) (:runtime-step! f))
        (do (sp/charge! f :turns 1) ((:runtime-step! f) f) (recur))
        :else (throw (ex-info "Original command boundary" {:phase phase :stage (:stage s)}))))))
(defn- take-call! [holder slot]
  ;; drain! transfers directly into this local; publishing into the already
  ;; allocated slot is nonallocating, before any observer/handoff.
  (let [value (drain! holder slot)]
    (aset ^objects slot 0 value) (aset ^objects slot 1 :owned) value))
(defn- select-header! [holder label]
  (let [s (live! holder) f (:frontend s) d (:driver f)
        helper (get-in s [:strict-driver :adapter :setup :helper-headers label])
        label (if helper label (sp/entry-label f label))
        header (or helper ((sp/host-helper "ensure-header!") d (sp/typed-name label)))
        c (j/register-headers (ctx s) [header])]
    (j/install-program! c (engine s)) (reset! (:current-ctx d) c)
    (when-not helper
      (let [original (cat/lookup (:catalogue d) (j/lean-name-data (j/request-value header "name")))]
        (need (= (:sha256 original) (j/request-value header "originalSha256")) "Call Header is not original catalogue row")))
    (exact-header! @holder header) [label header]))
(defn- call! [holder key label args argument-slots]
  (let [[label header] (select-header! holder label)
        slot (new-slot! holder key) s (live! holder)
        op {:kind :call :header header :label label :args args :argument-slots argument-slots :result-slot slot :stage :before-start}]
    (swap! holder assoc :operation op)
    (observe! holder :before-call! {:engine (engine s) :source (:source s) :header header :arguments args :stage (:stage s)})
    (sp/check-time! (:frontend s))
    (doseq [arg-slot argument-slots] (aset ^objects arg-slot 1 :start-pending))
    (j/start! (ctx s) (engine s) label args)
    (doseq [arg-slot (:argument-slots op)] (aset ^objects arg-slot 1 :transferred))
    ;; A start exception leaves the staged argument packet intact, never retry.
    (swap! holder assoc-in [:operation :stage] :started)
    (entry-live! @holder op)
    (let [value (take-call! holder slot)]
      ;; Separate, prepublished credit before exposing a borrowed observer alias.
      (retain! holder [key :shadow] value)
      (observe! holder :after-taken! {:engine (engine s) :source (:source s) :header header :result value :slot slot})
      (swap! holder assoc :operation nil) value)))
(defn- facade! [holder key value]
  (retain! holder key value)
  ;; Remains an owned extra credit until the actual start attempt; call! records
  ;; the uncertain claim interval and then the successful transfer explicitly.
  value)
(defn- call-borrowed! [holder key label values]
  (let [args (mapv (fn [[i v]] (facade! holder [key :arg i] v)) (map-indexed vector values))]
    (let [slots (mapv #(.get ^LinkedHashMap (:owners @holder) [key :arg %]) (range (count values)))
          result (call! holder key label args slots)]
      (doseq [i (range (count values))]
        (aset ^objects (.get ^LinkedHashMap (:owners @holder) [key :arg i]) 1 :transferred)) result)))
(defn- snapshot! [holder key]
  (let [s (live! holder) f (:frontend s)
        root (call-borrowed! holder [key :state] "ST.Prim.Ref.get" [0 0 (sp/owned f :state-ref) 0])
        sf (sp/ctor! f root 0 4) command (aget ^objects sf 0) cf (sp/ctor! f command 0 11)
        observation {:state root :environment (aget ^objects cf 0) :messages (aget ^objects cf 1)
                     :command-state command}]
    (retain! holder [key :env] (:environment observation))
    (retain! holder [key :messages] (:messages observation))
    (observe! holder :inspect-observation! {:engine (engine s) :source (:source s)
       :observation observation :capture (:capture @holder) :stage (:stage @holder)})
    observation))
(defn- release-slot! [holder key]
  (let [s (live! holder) slot (.get ^LinkedHashMap (:owners s) key)
        _ (need (= :owned (aget ^objects slot 1)) "Release occurrence is not owned")
        value (aget ^objects slot 0) unit (new-slot! holder [key :release-result])
        operation {:kind :release :owner-slot slot :result-slot unit :stage :before-start}]
    (swap! holder assoc :operation operation)
    (aset ^objects slot 1 :release-pending)
    (j/start-release! (ctx s) (engine s) value 1)
    (aset ^objects slot 1 :transferred)
    (need (= 0 (take-call! holder unit)) "Owner retirement must complete Unit")
    (aset ^objects unit 1 :immediate-consumed)
    (aset ^objects slot 0 nil)
    (swap! holder assoc :operation nil)))
(defn- clean-temporaries! [holder]
  ;; Keep one explicit final Env anchor; all other locally retained occurrences
  ;; retire through the callback-capable driver BEFORE issuing executable output.
  (let [entries (vec (.entrySet ^LinkedHashMap (:owners @holder)))
        keys (mapv #(.getKey ^java.util.Map$Entry %) (reverse entries))]
    (doseq [key keys
            :let [slot (.get ^LinkedHashMap (:owners @holder) key)]
            :when (and (= :owned (aget ^objects slot 1)) (not= key [:after :env]))]
      (release-slot! holder key))))
(defn- decode! [holder root]
  (let [s (live! holder) scope (decoder/open-decoder (ctx s) (engine s)
                              {:deadline-nanos (+ (System/nanoTime) 10000000000)
                               :max-nodes 20000 :max-output 50000 :max-depth 1000 :max-chars 1000000})]
    (try
      ;; JSON conversion creates owner-free host rows and canonical string keys.
      (json/read-str (json/write-str ((:project scope) [:list :decl] root)))
      (finally ((:close! scope))))))
(defn- ir-map! [decls]
  (need (<= (count decls) 64) "Local IR count exceeds first-profile bound")
  (reduce (fn [out d]
            (need (= #{"fdecl"} (set (keys d))) "Only ordinary generated fdecl accepted")
            (let [raw (get d "fdecl") name (get raw "f")]
              (need (not (contains? out name)) "Duplicate generated Name") (assoc out name raw))) {} decls))
(defn- static-calls! [raw]
  (loop [todo [raw] calls #{} work 0]
    (need (<= work 50000) "Generated structural walk bound")
    (if (empty? todo) calls
      (let [x (peek todo) todo (pop todo)]
        (cond
          (map? x)
          (do (need (not (contains? x "ap")) "Dynamic AP outside first generated profile")
              (recur (into todo (vals x))
                (reduce (fn [r k] (if-let [v (get x k)] (conj r (get v "c")) r)) calls ["fap" "pap"]) (inc work)))
          (vector? x) (recur (into todo x) calls (inc work))
          :else (recur todo calls (inc work)))))))
(defn- first-batch! [delta root-name boxed-name]
  ;; Exact original v17 compiler shape. Root borrows its Nat; only the genuine
  ;; boxed wrapper owns its entry credit. Preserve tobject lanes verbatim.
  (let [root (get delta root-name) boxed (get delta boxed-name)
        parameter {"idx" 1} result {"idx" 2}
        variable (fn [id] {"var" {"id" id}})
        params (fn [borrow] [{"x" parameter "borrow" borrow "ty" "tobject"}])]
    (need (and (= "tobject" (get root "type") (get boxed "type"))
               (= (params true) (get root "xs")) (= (params false) (get boxed "xs")))
          "First batch requires original borrowed tobject root and owned tobject boxed entry")
    (need (= ["inc" parameter 1 true false ["ret" (variable parameter)]] (get root "body"))
          "Root IR differs from original Nat identity compiler shape")
    (need (= ["vdecl" result "tobject" {"fap" {"c" root-name "ys" [(variable parameter)]}}
              ["dec" parameter 1 true false ["ret" (variable result)]]] (get boxed "body"))
          "Boxed IR is not the original owning root-call facade")
    (doseq [row [root boxed]]
      (need (set/subset? (static-calls! row) #{root-name boxed-name})
            "Generated static dependency frontier unsupported in first profile"))))
(defn- nat-const? [^Expr e]
  (and (= Expr/CONST (.-tag e)) (= (Name/mkStr Name/ANONYMOUS_NAME "Nat") (.-o0 e))
       (let [levels (.-o1 e)] (or (nil? levels) (and (.isArray (class levels)) (zero? (alength ^objects levels)))
                               (and (sequential? levels) (empty? levels))))))
(defn- identity-ci! [session version root]
  (#'adapter/validate-versions! session)
  (let [^ConstantInfo ci (.lookupLocal ^ansatz.kernel.Env (:env version) root)
        ^Expr type (when ci (.type ci)) ^Expr value (when ci (.value ci))]
    (need (and ci (= 1 (.tag ci)) (= 0 (.safety ci)) (empty? (.levelParams ci))
               (= [root] (vec (.all ci)))
               (= Expr/FORALL (.-tag type)) (nat-const? (.-o1 type)) (nat-const? (.-o2 type))
               (= Expr/LAM (.-tag value)) (nat-const? (.-o1 value))
               (= Expr/BVAR (.-tag ^Expr (.-o2 value))) (zero? (.-longVal ^Expr (.-o2 value))))
          "First code profile requires exact safe Nat unary identity CI") ci))
(defn- frozen-host [value]
  ;; Check depth/size and exact allowed host carriers BEFORE recursive JSON use.
  ;; No guest Nodes, CI objects, mutable arrays, receipts or arbitrary objects.
  (loop [pending [[value 0]] visits 0 chars 0]
    (need (and (<= visits 50000) (<= chars 1000000)) "Owner-free receipt data bound")
    (when (seq pending)
      (let [[v depth] (peek pending) tail (pop pending)]
        (need (<= depth 128) "Host receipt depth bound")
        (cond
          (map? v) (do (need (every? #(or (string? %) (keyword? %)) (keys v)) "Receipt map key must be text")
                       (recur (into tail (map #(vector % (inc depth)) (mapcat identity v))) (inc visits) chars))
          (vector? v) (recur (into tail (map #(vector % (inc depth)) v)) (inc visits) chars)
          (or (string? v) (keyword? v)) (recur tail (inc visits) (+ chars (count (str v))))
          (or (nil? v) (instance? Boolean v) (and (integer? v) (<= (.bitLength (biginteger v)) 4096)))
          (recur tail (inc visits) chars)
          :else (need false "Guest or mutable carrier cannot enter immutable code receipt")))))
  (letfn [(freeze [v]
            (cond
              (map? v) (let [entries (mapv (fn [[k x]] [(if (keyword? k) (name k) k) (freeze x)]) v)]
                         (need (= (count entries) (count (set (map first entries)))) "Receipt key encoding collision")
                         (into (sorted-map) entries))
              (vector? v) (mapv freeze v)
              (keyword? v) (name v)
              :else v))]
    (freeze value)))
(defn- digest [value]
  (let [bs (.getBytes ^String (json/write-str (frozen-host value)) java.nio.charset.StandardCharsets/UTF_8)]
    (need (<= (alength bs) 1000000) "Receipt serialization bound")
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (java.security.MessageDigest/getInstance "SHA-256") bs)))))
(defn open-command!
  "No effects; before-call source provider is independently trusted driver code.
   Source/provider capture occurs inside run-command! before any compiler getter."
  [frontend strict-driver {:keys [root-label layout-directory source-captures]}]
  (need (and (string? root-label) (re-matches #"[A-Za-z_][A-Za-z0-9_]*" root-label)) "Simple top-level root Name required")
  (let [hooks (get-issued providers source-captures) session (:adapter strict-driver)
        e (:engine (:driver frontend)) token (CommandRun.)
        holder (atom {:status :open :stage :open :thread (Thread/currentThread) :frontend frontend :strict-driver strict-driver
                      :source (:source (:driver frontend)) :hooks hooks :root-label root-label
                      :layout (#'authority/read-layout! layout-directory) :owners (LinkedHashMap.)})]
    (live! holder)
    (need (and (identical? e (:engine session)) (= "idle" (j/phase (ctx @holder) e))
               (not= :active @(:phase session)) (nil? @(:invocation session)) (nil? @(:in-flight frontend))) "Command requires idle, fully replied adapter")
    (put-issued runs token holder)))
(defn owner-packet [run]
  (let [s (state run)] {:status (:status s) :stage (:stage s) :operation (:operation s)
                        :owners (:owners s) :failure (:failure s)}))
(defn run-command! [run]
  (let [holder (get-issued runs run) s (live! holder) f (:frontend s) session (:adapter (:strict-driver s)) e (engine s)]
    (need (= :open (:status s)) "Command can execute only once")
    (locking busy-engines
      (need (not (.containsKey busy-engines e)) "This engine already has a command receipt controller")
      (.put busy-engines e true))
    (swap! holder assoc :status :running :stage :capture)
    (try
      (let [capture (observe! holder :before-command! {:engine e :source (:source s) :frontend f
                      :input (sp/owned f :input) :state-ref (sp/owned f :state-ref)})
            _ (need (and (identical? e (:engine capture)) (identical? (:source s) (:source capture))
                         (identical? (sp/owned f :input) (:input capture))
                         (identical? (sp/owned f :state-ref) (:state-ref capture))) "Independent source witness lacks actual roots")
            _ (swap! holder assoc :capture capture :stage :baseline)
            initial (snapshot! holder :before)
            before-version @(:published-count session)
            baseline (ir-map! (decode! holder (call-borrowed! holder :baseline "Lean.IR.getDecls" [(:environment initial)])))
            _ (swap! holder assoc :stage :process-command)
            _ (sp/charge! f :commands 1)
            result (call-borrowed! holder :process "Lean.Elab.Frontend.processCommand" [(sp/owned f :input) (sp/owned f :state-ref) 0])
            done (aget ^objects (sp/ctor! f result 0 1) 0)
            _ (need (and (instance? Long done) (= 0 done)) "Expected definition command, not EOF")
            _ (need (and (= :replied @(:phase session)) (nil? @(:invocation session))
                         (= (inc before-version) @(:published-count session))) "Exactly one fully replied strict publication required")
            _ (swap! holder assoc :stage :observed)
            after (snapshot! holder :after)
            errors (call-borrowed! holder :errors "Lean.MessageLog.hasErrors" [(:messages after)])
            _ (need (and (instance? Long errors) (= 0 errors)) "Compiler or elaborator diagnostics reported failure")
            version (peek @(:versions session))
            root (Name/mkStr Name/ANONYMOUS_NAME (:root-label s))
            ci (identity-ci! session version root)
            actual (#'authority/environment-view! (:driver f) (:layout s) (:environment after))
            published (#'authority/kernel-view! (:driver f) (:layout s) (aget ^objects (:kernel-root version) 0))
            _ (need (and (identical? (:constant-map actual) (aget ^objects (:constant-map version) 0))
                         (identical? (:const2mod-map actual) (:const2mod-map published))
                         (every? true? (map identical? (rest (:header-fields actual)) (rest (:header-fields published)))))
                    "Final compiler Env changed published map/imported header witness")
            _ (swap! holder assoc :stage :readback)
            post (ir-map! (decode! holder (call-borrowed! holder :post "Lean.IR.getDecls" [(:environment after)])))
            _ (doseq [[name row] baseline] (need (= row (get post name)) "Compiler changed an old local IR row"))
            delta (apply dissoc post (keys baseline))
            root-name (sp/typed-name (:root-label s)) boxed-name ["str" root-name "_boxed"]
            _ (need (= #{root-name boxed-name} (set (keys delta))) "First batch must contain exactly root and original boxed companion")
            _ (doseq [name (keys delta)]
                (need (nil? (cat/lookup (get-in f [:driver :catalogue]) name)) "Generated Name overlaps original catalogue domain"))
            _ (first-batch! delta root-name boxed-name)
            rows (mapv (fn [name] {"kind" "decl" "name" name "ir" {"fdecl" (get delta name)}}) [root-name boxed-name])
            _ (swap! holder assoc :stage :cleanup)
            _ (clean-temporaries! holder)
            _ (#'adapter/validate-versions! session)
            ;; Cleanup may demand original finalizer bodies; capture its actual
            ;; descendant only AFTER every callback-capable temporary release.
            _ (swap! holder assoc :stage :prepare)
            base (ctx @holder)
            prepared (j/extend-program base rows)
            ;; Program.extend deliberately ignores non-declaration envelopes.
            ;; Check real prepared entries before issuing any linking authority.
            _ (doseq [label [(:root-label s) (str (:root-label s) "._boxed")]]
                (j/function-id prepared label))
            _ (#'adapter/validate-versions! session)
            description (frozen-host (:description capture))
            _ (need (map? description) "Independent source profile description required")
            summary {:schema "original-compiler-nat-identity/1" :root root-name :boxed-entry boxed-name
                     :rows-sha256 (digest rows) :profile-description description :row-count 2
                     :root-abi {:parameters [{:type "tobject" :borrow true}] :result "tobject"}
                     :boxed-abi {:parameters [{:type "tobject" :borrow false}] :result "tobject"}
                     :checked-version (:id version) :input-description-sha256 (digest description)
                     :initializers [] :static-frontier [] :native-physical-parity false}
            batch (CodeBatch.)]
        ;; Registry holds live custody, never inserted into Program or public summary.
        (swap! holder assoc :stage :sealed :status :sealed :version version :ci ci :base-program (:program base)
               :prepared prepared :summary summary :rows rows)
        (put-issued batches batch holder)
        {:status :sealed :batch batch :summary summary})
      (catch Throwable error
        (let [message (or (.getMessage error) (.getName (class error)))]
          (swap! holder assoc :status :failed :failure {:class (.getName (class error)) :message (subs message 0 (min 900 (count message)))})
          {:status :failed :run run :stage (:stage @holder) :failure (:failure @holder)})))))
(defn batch-summary [batch] (:summary @(get-issued batches batch)))
(defn run-eof!
  "Separate original EOF transaction. No declaration/code authority is issued.
   SourceCaptures must independently authenticate the terminal source position."
  [run]
  (let [holder (get-issued runs run) s (live! holder) f (:frontend s)
        session (:adapter (:strict-driver s)) e (engine s)]
    (need (= :open (:status s)) "EOF can execute only once")
    (locking busy-engines
      (need (not (.containsKey busy-engines e)) "This engine already has a command receipt controller")
      (.put busy-engines e true))
    (swap! holder assoc :status :running :stage :capture)
    (try
      (let [capture (observe! holder :before-command! {:engine e :source (:source s) :frontend f
                      :input (sp/owned f :input) :state-ref (sp/owned f :state-ref)})
            _ (need (and (identical? e (:engine capture)) (identical? (:source s) (:source capture))
                         (identical? (sp/owned f :input) (:input capture))
                         (identical? (sp/owned f :state-ref) (:state-ref capture))) "EOF source witness lacks actual roots")
            _ (swap! holder assoc :capture capture :stage :baseline)
            initial (snapshot! holder :before)
            version (peek @(:versions session)) before-version @(:published-count session)
            _ (need version "EOF profile requires a prior checked declaration")
            initial-errors (call-borrowed! holder :initial-errors "Lean.MessageLog.hasErrors" [(:messages initial)])
            _ (need (and (instance? Long initial-errors) (= 0 initial-errors)) "EOF cannot erase prior diagnostics")
            initial-actual (#'authority/environment-view! (:driver f) (:layout s) (:environment initial))
            initial-published (#'authority/kernel-view! (:driver f) (:layout s) (aget ^objects (:kernel-root version) 0))
            _ (need (and (identical? (:constant-map initial-actual) (aget ^objects (:constant-map version) 0))
                         (identical? (:const2mod-map initial-actual) (:const2mod-map initial-published))
                         (every? true? (map identical? (rest (:header-fields initial-actual)) (rest (:header-fields initial-published)))))
                    "EOF input differs from the captured checked version")
            baseline (ir-map! (decode! holder (call-borrowed! holder :baseline "Lean.IR.getDecls" [(:environment initial)])))
            _ (swap! holder assoc :stage :process-command)
            _ (sp/charge! f :commands 1)
            result (call-borrowed! holder :process "Lean.Elab.Frontend.processCommand" [(sp/owned f :input) (sp/owned f :state-ref) 0])
            done (aget ^objects (sp/ctor! f result 0 1) 0)
            _ (need (and (instance? Long done) (= 1 done)) "Expected actual EOF result")
            _ (need (and (= :replied @(:phase session)) (nil? @(:invocation session))
                         (= before-version @(:published-count session))
                         (identical? version (peek @(:versions session)))) "EOF unexpectedly published a declaration")
            _ (swap! holder assoc :stage :observed)
            after (snapshot! holder :after)
            errors (call-borrowed! holder :errors "Lean.MessageLog.hasErrors" [(:messages after)])
            _ (need (and (instance? Long errors) (= 0 errors)) "EOF diagnostics reported failure")
            actual (#'authority/environment-view! (:driver f) (:layout s) (:environment after))
            published (#'authority/kernel-view! (:driver f) (:layout s) (aget ^objects (:kernel-root version) 0))
            _ (need (and (identical? (:constant-map actual) (aget ^objects (:constant-map version) 0))
                         (identical? (:const2mod-map actual) (:const2mod-map published))
                         (every? true? (map identical? (rest (:header-fields actual)) (rest (:header-fields published)))))
                    "EOF changed published map/imported header witness")
            _ (swap! holder assoc :stage :readback)
            post (ir-map! (decode! holder (call-borrowed! holder :post "Lean.IR.getDecls" [(:environment after)])))
            _ (need (= baseline post) "EOF changed local generated code")
            _ (swap! holder assoc :stage :cleanup)
            _ (clean-temporaries! holder)
            _ (#'adapter/validate-versions! session)
            summary {:schema "original-compiler-eof/1" :checked-version (:id version)
                     :row-count 0 :profile-description (frozen-host (:description capture))}]
        (swap! holder assoc :stage :eof-sealed :status :eof-sealed :summary summary)
        {:status :eof-sealed :summary summary})
      (catch Throwable error
        (let [message (or (.getMessage error) (.getName (class error)))]
          (swap! holder assoc :status :failed :failure {:class (.getName (class error)) :message (subs message 0 (min 900 (count message)))})
          {:status :failed :run run :stage (:stage @holder) :failure (:failure @holder)})))))
(defn rebase-idle-deadline!
  "Explicit allowance for host REPL idle time only. Preserves owner/command/code
   counters and continuations. Terminal or running operations cannot be resumed."
  [run milliseconds]
  (let [holder (get-issued runs run) s (live! holder) f (:frontend s)]
    (need (and (integer? milliseconds) (<= 1 milliseconds 60000)
               (contains? #{:open :sealed :linked :eof-sealed} (:status s))
               (= "idle" (j/phase (ctx s) (engine s)))
               (nil? @(:in-flight f))) "Deadline rebase requires healthy idle custody")
    (swap! holder assoc-in [:frontend :deadline-nanos]
           (+ (System/nanoTime) (* 1000000 milliseconds)))
    {:status :idle-deadline-rebased :milliseconds milliseconds :budget @(:used f)}))
(defn link-batch! [batch driver]
  (let [holder (get-issued batches batch) s (live! holder) f (:frontend s) c (ctx s) e (engine s)]
    (need (and (= :sealed (:status s)) (identical? driver (:driver f))
               (= "idle" (j/phase c e)) (identical? (:program c) (:base-program s))) "Link only exact sealed compilation branch/base Program")
    (#'adapter/validate-versions! (:adapter (:strict-driver s)))
    (need (identical? (:version s) (peek @(:versions (:adapter (:strict-driver s)))) ) "Checked version advanced after compilation")
    (swap! holder assoc :stage :install-pending)
    (try
      (j/install-program! (:prepared s) e)
      (reset! (:current-ctx driver) (:prepared s))
      (need (and (identical? (:program (:prepared s)) (field e "program"))
                 (identical? (:program (:prepared s)) (:program @(:current-ctx driver))))
            "Prepared Program was not published on the actual execution branch")
      (swap! holder assoc :status :linked :stage :linked)
      {:status :linked :summary (:summary s) :boxed-label (str (:root-label s) "._boxed")}
      (catch Throwable error (swap! holder assoc :status :failed :stage :install-failed) (throw error)))))

(defn retire!
  "Retire only this controller's healthy actual owner occurrences. Failure work
   remains inspectable and is never auto-unwound. Revokes future batch linking;
   does not close frontend/base/Run/catalogue or roll back an installed Program."
  [run]
  (let [holder (get-issued runs run) s (live! holder)]
    (need (contains? #{:sealed :linked :eof-sealed} (:status s)) "Only healthy completed command custody can retire")
    (need (= "idle" (j/phase (ctx s) (engine s))) "Retirement requires idle engine")
    (swap! holder assoc :stage :retirement)
    (try
      (release-slot! holder [:after :env])
      (reset! holder {:status :retired :stage :retired :summary (:summary s)})
      ;; Only successful explicit retirement releases this engine's controller
      ;; reservation. Failed/unfinished branches stay quarantined.
      (locking busy-engines (.remove busy-engines (engine s)))
      {:status :retired}
      (catch Throwable error
        (swap! holder assoc :status :failed :stage :retirement-failed)
        (throw error)))))
