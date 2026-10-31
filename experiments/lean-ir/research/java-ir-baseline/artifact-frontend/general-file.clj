(ns general-frontend-file-v1
  "Bounded general command/file orchestration over one explicitly prepared branch.
   No branch constructor, source-language recognizer, implicit import or unwind."
  (:refer-clojure :exclude [load!])
  (:require [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [heartbeat-lab-options-proof :as options]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [java-matched-artifact-base-v1 :as base]
            [general-frontend-source-provider-v1 :as provider]
            [general-command-receipt-v1 :as command]
            [general-generated-batch-v1 :as batch])
  (:import [java.util WeakHashMap] [java.math BigInteger]
           [ansatz.kernel Env Expr Name ConstantInfo]))
(deftype FileRun [])
(defonce ^:private files (WeakHashMap.))
(defonce ^:private busy (WeakHashMap.))
(defn- need [ok text] (when-not ok (throw (ex-info text {:profile :general-frontend-file-v1}))))
(defn- cell [file] (locking files (or (.get files file) (throw (ex-info "Actual issued general FileRun required" {})))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- driver [s] (get-in s [:bundle :child :driver]))
(defn- context [s] @(:current-ctx (driver s)))
(defn- engine [s] (:engine (driver s)))
(defn- live! [holder]
  (let [s @holder]
    (need (identical? (:thread s) (Thread/currentThread)) "File is thread confined")
    (need (not (contains? #{:failed :closed} (:status s))) "File is terminal")
    (let [d (driver s) e (engine s) a (get-in s [:bundle :admission :adapter])]
      (source/guard-source! (get-in s [:bundle :child :code-receipt]) (:source d))
      (need (and (identical? e (:engine a)) (identical? (:source d) (:source a))
                 (identical? (:program (context s)) (field e "program"))) "File source/adapter/current Program differs")
      (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
        (need (false? (field e k)) "File engine is terminal or advancing"))
      (#'adapter/validate-versions! a)) s))
(defn- failed! [holder error]
  (swap! holder assoc :status :failed :failure (command/failure-summary error)))
(defn inspect [file]
  (select-keys @(cell file) [:status :stage :next-command :commands :execution :failure :retirement :elapsed-ms]))
(defn owner-packet
  "Borrowed diagnostic aliases only; no retry, release or checking authority."
  [file]
  (let [s @(cell file)]
    {:status (:status s) :stage (:stage s) :failure (:failure s) :invocation (:invocation s)
     :active-command (when-let [r (:active s)] (command/owner-packet r))
     :pending-code (:pending-code s) :branch (:bundle s) :source-provider (:provider s) :generated-scope (:scope s)}))
(defn open-file!
  "BUNDLE contains actual :child/:frontend/:admission; CAPTURE is independently
   checked against actual InputContext by the original-source provider. HEADERS
   are the authenticated companion entry/caller/gate and original parser helper.
   CLOSE-BRANCH! is explicit trusted host orchestration over this same bundle.
   Failure after preparation starts returns a failed token with its owner packet."
  [bundle capture {:keys [headers layout-directory close-branch! quantum row-limit max-commands]
                   :or {quantum 1000 row-limit 2048 max-commands 128}}]
  (need (and (map? headers) (fn? close-branch!) (string? layout-directory) (seq layout-directory)
             (integer? quantum) (<= 100 quantum 10000) (integer? row-limit) (<= 1 row-limit 2048)
             (integer? max-commands) (<= 1 max-commands 128)) "Explicit bounded file/source/disposal policy required")
  (let [e (get-in bundle [:child :driver :engine]) marker (Object.)
        holder (atom {:thread (Thread/currentThread) :status :preparing :stage :preflight
                      :bundle bundle :capture capture :layout-directory layout-directory :headers headers
                      :close-branch! close-branch! :quantum quantum :row-limit row-limit :max-commands max-commands
                      :marker marker :next-command 0 :commands [] :entries {} :execution :supported :active nil})
        token (FileRun.)]
    (live! holder)
    (need (and (= "idle" (j/phase (context @holder) e))
               (nil? @(get-in bundle [:frontend :in-flight]))) "File requires genuinely idle prepared frontend")
    (locking busy (need (nil? (.get busy e)) "Another file owns this engine") (.put busy e marker))
    (locking files (.put files token holder))
    (try
      (swap! holder assoc :stage :provider-opening)
      (let [p (provider/open-provider! (:child bundle) (:frontend bundle) capture {:layout-directory layout-directory})]
        (swap! holder assoc :provider p :stage :captures-opening)
        (let [captures (command/source-captures (get-in bundle [:child :code-receipt])
                        (assoc (provider/callbacks p) :headers headers))]
          (swap! holder assoc :captures captures :stage :scope-opening)
          (let [scope (batch/open-scope! (get-in bundle [:child :driver]) (get-in bundle [:admission :adapter]))]
            (swap! holder assoc :scope scope :status :open :stage :idle))))
      (catch Throwable error (failed! holder error))) token))
(defn- linked-entries [s receipt]
  (command/with-command! receipt
    (fn [view]
      (let [index (#'batch/program-index (:program (context s)) (:source (driver s)))]
        (into {} (for [[name ir] (:delta view)
                      :let [h (get-in index [(source/label name) :header])]]
                   (do (need (and h (= name (j/lean-name-data (j/request-value h "name"))))
                             "Linked generated Header identity differs")
                       [name {:header h :ir ir}])))))))
(defn next-command!
  "One actual source command, including genuine eoi. Code unsupported is recorded
   independently of successful checking; no fake EOF or failure resumption."
  [file]
  (let [holder (cell file) s (live! holder)]
    (need (and (= :open (:status s)) (nil? (:active s))) "File is not at a next-command boundary")
    (if (>= (:next-command s) (:max-commands s))
      (do (swap! holder assoc :status :stopped :stage :command-limit) (inspect file))
      (do
    (swap! holder assoc :status :loading :stage :command-opening)
    (try
      (let [f (options/rebase-idle-deadline (get-in s [:bundle :frontend]))
            _ (swap! holder assoc-in [:bundle :frontend] f)
            run (command/open-command! f (get-in s [:bundle :admission]) (:captures s)
                                       (select-keys s [:layout-directory :quantum :row-limit]))
            _ (swap! holder assoc :active run :stage :command-running)
            result (command/run-command! run)
            _ (need (= :sealed (:status result)) "Original command failed; inspect active owner packet")
            _ (swap! holder assoc :stage :code-preparing)
            prepared (batch/prepare-batch! (:scope s) (:receipt result))
            _ (swap! holder assoc :pending-code prepared)
            _ (need (contains? #{:empty :unsupported :prepared} (:status prepared)) "Unknown generated-code result")
            linked (when (= :prepared (:status prepared)) (batch/link-batch! (:batch prepared)))
            _ (when linked (need (= :linked (:status linked)) "Generated batch did not link"))
            entries (if linked (linked-entries @holder (:receipt result)) {})
            summary (:summary result)
            record {:command summary :code (dissoc prepared :batch) :link linked}
            _ (swap! holder assoc :stage :command-retiring)
            _ (command/rebase-idle-deadline! run 60000)
            _ (command/retire! run)
            kind (:kind summary)]
        (swap! holder (fn [v] (-> v (update :commands conj record) (update :entries merge entries)
                                  (update :next-command inc) (assoc :active nil :pending-code nil :stage :idle)
                                  (cond-> (= :unsupported (:status prepared)) (assoc :execution :unsupported)))))
        (case kind
          :command (swap! holder assoc :status :open)
          :eoi (swap! holder assoc :status (if (= :supported (:execution @holder)) :ready :unsupported)
                       :stage :eoi :linked-program (:program (context @holder))
                       :checked-version (peek @(get-in @holder [:bundle :admission :adapter :versions])))
          (swap! holder assoc :status :stopped :stage kind))
        (inspect file))
      (catch Throwable error (failed! holder error) (inspect file)))))))
(defn load!
  "Consume up to the explicit command bound. Stops on actual eoi, explicit
   exit/import, unsupported execution at eoi, or quarantined failure."
  [file]
  (let [holder (cell file) started (System/nanoTime)]
    (need (= :open (:status (live! holder))) "Load requires an open file")
    (loop []
      (let [result (next-command! file)]
        (if (= :open (:status result)) (recur)
          (do (swap! holder assoc :elapsed-ms (/ (- (System/nanoTime) started) 1e6)) (inspect file)))))))
(defn- nat! [value]
  (need (or (and (= Long (class value)) (<= 0 value))
            (and (= BigInteger (class value)) (not (neg? (.signum ^BigInteger value))) (<= (.bitLength ^BigInteger value) 4096)))
        "Exact bounded immutable Nat required") value)
(defn- kernel-name [typed]
  (#'batch/typed-name! typed)
  (let [parts (loop [n typed out []] (if (= ["anonymous"] n) out (recur (second n) (conj out [(first n) (nth n 2)]))))]
    (reduce (fn [prefix [kind leaf]]
              (if (= "str" kind) (Name/mkStr prefix leaf)
                (Name/mkNum prefix (.longValue (BigInteger. (str leaf)))))) Name/ANONYMOUS_NAME (reverse parts))))
(defn- nat-constant? [x]
  (and (instance? Expr x) (= Expr/CONST (.-tag ^Expr x)) (= (Name/mkStr Name/ANONYMOUS_NAME "Nat") (.-o0 ^Expr x))
       (let [levels (.-o1 ^Expr x)] (or (nil? levels) (and (instance? java.util.List levels) (empty? levels))
                                                   (and (= (class (object-array 0)) (class levels)) (zero? (alength ^objects levels)))))))
(defn- nat-entry! [s name]
  (#'batch/typed-name! name)
  (let [{:keys [header ir]} (get-in s [:entries name]) d (driver s) index (#'batch/program-index (:program (context s)) (:source d))
        declaration (:declaration ir)]
    (need (and header (= "fdecl" (:kind ir)) (identical? header (get-in index [(source/label name) :header]))
               (= "str" (first name)) (= "_boxed" (nth name 2))
               (= ["tobject"] (vec (j/request-value header "paramTypes")))
               (= [false] (vec (j/request-value header "borrowed"))) (= "tobject" (j/request-value header "resultType"))
               (= [{"borrow" false "ty" "tobject"}] (mapv #(select-keys % ["borrow" "ty"]) (get declaration "xs"))))
          "Entry must be this file's canonical linked owned unary boxed fdecl")
    (let [session (get-in s [:bundle :admission :adapter]) version (:checked-version s)]
      (base/with-version! (:matched-base session) (:env version)
        (fn [^Env env]
          (let [^ConstantInfo ci (.lookupLocal env (kernel-name (second name))) ^Expr type (when ci (.-type ci))]
            (need (and ci (= ConstantInfo/DEF (.-tag ci)) (zero? (.-safety ci))
                       (zero? (alength ^objects (.-levelParams ci))) type (= Expr/FORALL (.-tag type))
                       (nat-constant? (.-o1 type)) (nat-constant? (.-o2 type)))
                  "Current checked local declaration is not safe monomorphic Nat to Nat"))))) header))
(defn- drain-invocation! [holder slot]
  (loop []
    (let [s (live! holder) f (get-in s [:bundle :frontend]) c (context s) e (engine s) phase (j/phase c e)]
      (sp/check-time! f)
      (case phase
        "complete" (do (aset ^objects slot 1 :take-pending)
                       (let [v (j/take-result! c e)] (aset ^objects slot 0 v) (aset ^objects slot 1 :owned) v))
        "running" (let [left (- (get-in f [:limits :instructions]) (:instructions @(:used f))) before (j/instructions c e)]
                    (need (pos? left) "File invocation instruction budget exhausted") (sp/charge! f :turns 1)
                    (j/advance! c e (min (:quantum s) left))
                    (sp/charge! f :instructions (- (j/instructions (context @holder) e) before)) (recur))
        "code-call" (do (sp/charge! f :turns 1) (sp/charge! f :code-requests 1) (demand/service-code! (driver s)) (recur))
        (if (contains? #{"host-call" "host-guest-result"} phase)
          (do (sp/charge! f :turns 1) ((:runtime-step! f) f) (recur))
          (throw (ex-info "Unsupported file invocation boundary" {:phase phase})))))))
(defn invoke-nat!
  "Exact typed boxed entry from this completed file, checked local Nat to Nat
   type and immutable bounded Nat codec. Does not predict the function result."
  [file entry argument]
  (let [holder (cell file) s (live! holder) n (nat! argument)]
    (need (and (= :ready (:status s)) (nil? (:active s)) (= "idle" (j/phase (context s) (engine s)))
               (identical? (:linked-program s) (:program (context s)))
               (identical? (:checked-version s) (peek @(get-in s [:bundle :admission :adapter :versions]))))
          "Invoke requires this completed file's exact checked version and linked Program")
    (nat-entry! s entry)
    (let [f (options/rebase-idle-deadline (get-in s [:bundle :frontend])) slot (object-array [nil :unclaimed])]
      (swap! holder assoc-in [:bundle :frontend] f)
      (sp/check-time! f)
      (swap! holder assoc :status :invoking :stage :invocation-starting :invocation {:entry entry :argument n :result slot})
      (try
        (j/start! (context @holder) (engine s) (source/label entry) [n])
        (swap! holder assoc :stage :invocation-running)
        (let [result (drain-invocation! holder slot)]
          (nat! result) (aset slot 1 :transferred)
          (swap! holder #(-> % (assoc :status :ready :stage :eoi) (dissoc :invocation))) result)
        (catch Throwable error (failed! holder error) (throw error))))))
(defn close!
  "Close only healthy idle custody; source/scope revoke before actual branch
   retirement. A failure preserves all remaining journals and never retries."
  [file]
  (let [holder (cell file) s (live! holder) e (engine s)]
    (need (and (contains? #{:ready :unsupported :stopped} (:status s)) (nil? (:active s))
               (= "idle" (j/phase (context s) e))) "Close requires healthy terminal file custody")
    (swap! holder assoc :status :closing :stage :closing)
    (try
      (provider/close! (:provider s)) (batch/close! (:scope s))
      (let [retirement ((:close-branch! s) (:bundle s))]
        (need (true? (field e "closed")) "Branch retirement did not close the actual engine")
        (locking busy (.remove busy e))
        (reset! holder (assoc (select-keys s [:thread :commands :next-command :execution :elapsed-ms])
                             :status :closed :stage :closed :retirement retirement))
        (inspect file))
      (catch Throwable error (failed! holder error) (throw error)))))
