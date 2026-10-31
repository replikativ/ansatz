(ns filesystem-nat-file-run-v1
  "Retained, finite filesystem frontend experiment. A trusted host supplies an
   actual prepared branch and its disposal hook; no public runtime constructor."
  (:require [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [heartbeat-lab-options-proof :as options]
            [ansatz.research.ir.source-setup :as source]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [generated-command-receipt-v1 :as command]
            [filesystem-nat-source-profile-v2 :as profile]
            [filesystem-nat-source-provider-v2 :as provider])
  (:import [java.util WeakHashMap]))
(deftype FileRun [])
(defonce ^:private files (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :filesystem-nat-file-run-v1}))))
(defn- cell [file] (locking files (or (.get files file) (throw (ex-info "Issued FileRun required" {})))))
(defn- live! [holder]
  (let [s @holder]
    (need (and (identical? (:thread s) (Thread/currentThread))
               (not (contains? #{:failed :closed} (:status s)))) "File is terminal or belongs to another thread")
    (let [d (get-in s [:bundle :child :driver]) c @(:current-ctx d)]
    (source/guard-source! (get-in s [:bundle :child :code-receipt]) (:source d))
    (need (identical? (:engine d) (get-in s [:bundle :admission :adapter :engine])) "File branch differs from checked adapter")
    (need (identical? (:program c) (#'command/field (:engine d) "program")) "File driver and execution Program differ")
    (#'adapter/validate-versions! (get-in s [:bundle :admission :adapter]))
    s)))
(defn open-file!
  "Capture was read by prototype.project-source and is independently checked
   against actual guest InputContext by each SourceCaptures factory. BUNDLE is
   trusted host orchestration, not an authority inferred from descriptive maps."
  [bundle capture {:keys [close-branch! layout-directory]
                   :or {layout-directory "../../target/java-kernel-shim-overlay-v1"}}]
  (need (fn? close-branch!) "Explicit trusted branch disposal hook required")
  (need (and (string? layout-directory) (seq layout-directory)) "Explicit compiled layout directory required")
  (let [p (profile/captured-profile capture)
        token (FileRun.) holder (atom {:status :open :thread (Thread/currentThread)
          :bundle bundle :capture capture :profile p :close-branch! close-branch! :layout-directory layout-directory
          :receipts [] :next-command 0 :active nil})]
    (live! holder)
    (need (= "idle" (j/phase (sp/ctx (:frontend bundle)) (sp/engine (:frontend bundle)))) "File requires idle prepared frontend")
    (locking files (.put files token holder)) token))
(defn inspect [file]
  (let [s @(cell file)]
    (select-keys s [:status :next-command :receipts :failure :elapsed-ms :source :retirement])))
(defn owner-packet
  "Borrowed failure diagnostics only. No retry, receipt or unwind authority."
  [file]
  (let [s @(cell file)]
    {:status (:status s) :failure (:failure s) :invocation (:invocation s)
     :active-command (when-let [run (:active s)] (command/owner-packet run))
     :branch (:bundle s)}))
(defn load! [file]
  (let [holder (cell file) s (live! holder) started (System/nanoTime)]
    (need (= :open (:status s)) "File can load only once")
    (swap! holder assoc :status :loading :source (select-keys (:profile s) [:sha256 :byte-count :module :filename :command-count]))
    (try
      (doseq [i (range (inc (get-in s [:profile :command-count])))]
        (let [state (live! holder) bundle (:bundle state) child (:child bundle)
              frontend (options/rebase-idle-deadline (:frontend bundle))
              transaction-start (System/nanoTime) before-budget @(:used frontend)
              _ (swap! holder assoc-in [:bundle :frontend] frontend)
              eof? (= i (get-in state [:profile :command-count]))
              root (if eof? "__EOF__" (get-in state [:profile :commands i :root]))
              captures (provider/make-captures! child frontend (:capture state) i {:layout-directory (:layout-directory state)})
              run (command/open-command! frontend (:admission bundle)
                    {:root-label root :layout-directory (:layout-directory state) :source-captures captures})
              _ (swap! holder assoc :active run)
              result (if eof? (command/run-eof! run) (command/run-command! run))
              _ (need (= (if eof? :eof-sealed :sealed) (:status result)) (str "Original file transaction failed: " (pr-str (dissoc result :run :batch))))
              linked (when-not eof? (command/link-batch! (:batch result) (:driver child)))]
          (swap! holder update :receipts conj
                 {:action (if eof? :eof :definition) :summary (:summary result) :linked? (boolean linked)
                  :elapsed-ms (/ (- (System/nanoTime) transaction-start) 1e6)
                  :budget-delta (into {} (for [[k value] @(:used frontend)] [k (- value (get before-budget k 0))]))})
          (command/retire! run)
          (swap! holder assoc :active nil :next-command (inc i))))
      (let [final (live! holder) driver (get-in final [:bundle :child :driver])]
        (swap! holder assoc :status :ready :linked-program (:program @(:current-ctx driver))
               :checked-version (peek @(get-in final [:bundle :admission :adapter :versions]))
               :elapsed-ms (/ (- (System/nanoTime) started) 1e6)))
      (inspect file)
      (catch Throwable error
        (swap! holder assoc :status :failed :failure {:class (.getName (class error)) :message (.getMessage error)})
        (inspect file)))))
(defn invoke-nat! [file root n]
  (let [holder (cell file) s (live! holder) d (get-in s [:bundle :child :driver]) c @(:current-ctx d) e (:engine d)]
    (need (and (= :ready (:status s))
               (contains? (set (map :root (get-in s [:profile :commands]))) root)
               (or (and (instance? Long n) (<= 0 n)) (and (= java.math.BigInteger (class n)) (not (neg? (.signum ^java.math.BigInteger n)))))
               (identical? (:program c) (:linked-program s))
               (identical? (:checked-version s) (peek @(get-in s [:bundle :admission :adapter :versions])))
               (= "idle" (j/phase c e))) "Invocation requires this completed file, original linked version and a Nat")
    (swap! holder assoc :status :invoking :invocation {:stage :before-start :entry (str root "._boxed") :argument n})
    (try
      (j/start! c e (str root "._boxed") [n])
      (swap! holder assoc-in [:invocation :stage] :started)
      (loop [left 10000]
        (case (j/phase c e)
          "complete" (let [result (j/take-result! c e)]
                       (swap! holder assoc-in [:invocation :result] result)
                       (need (= n result) "Finite identity execution differed")
                       (swap! holder #(-> % (assoc :status :ready) (dissoc :invocation))) result)
          "running" (do (need (pos? left) "Identity execution budget exceeded") (j/advance! c e (min 100 left)) (recur (- left (min 100 left))))
          (throw (ex-info "Unexpected finite identity runtime boundary" {:phase (j/phase c e)}))))
      (catch Throwable error
        (swap! holder assoc :status :failed :failure {:class (.getName (class error)) :message (.getMessage error)})
        (throw error)))))
(defn close! [file]
  (let [holder (cell file) s (live! holder)]
    (need (and (= :ready (:status s)) (nil? (:active s))) "Close requires a completely loaded idle file")
    (swap! holder assoc :status :closing)
    (try
      (let [retirement ((:close-branch! s) (:bundle s))]
        (reset! holder (assoc (select-keys s [:source :receipts :elapsed-ms :next-command]) :status :closed :retirement retirement))
        (inspect file))
      (catch Throwable error
        (swap! holder assoc :status :failed :failure {:class (.getName (class error)) :message (.getMessage error)})
        (throw error)))))
