(ns source-module-project-v1
  "Bounded same-engine file coordination. Captures describe work; only actual
   M1/M2/export/closure capabilities establish checked artifacts. No Env factory,
   implicit import, branch constructor or automatic failure unwind."
  (:require [general-frontend-source-provider-v1 :as provider]
            [general-command-receipt-v1 :as command]
            [general-generated-batch-v1 :as batch]
            [java-source-module-exchange-v1 :as exchange]
            [source-import-frontend-setup-v1 :as imports]
            [heartbeat-lab-options-proof :as options])
  (:import [java.util WeakHashMap]))
(deftype Project [])
(defonce ^:private projects (WeakHashMap.))
(defn- need [ok text] (when-not ok (throw (ex-info text {:profile :source-module-project-v1}))))
(defn- module-name! [segments]
  (need (and (vector? segments) (<= 1 (count segments) 128)
             (every? #(and (string? %) (<= 1 (count %) 4096)
                           (not (re-find #"[.\\/\u0000]" %))) segments))
        "Bounded exact module segments required")
  (reduce (fn [prefix segment] ["str" prefix segment]) ["anonymous"] segments))
(defn plan-project
  "Pure bounded dependency order. This metadata never authenticates imports;
   original parser/opaque closure checks remain mandatory at execution."
  [entries]
  (need (and (vector? entries) (<= 1 (count entries) 16)) "Project requires one to sixteen captured files")
  (:files
    (reduce (fn [{:keys [files seen paths bytes edges] :as state} {:keys [capture dependencies]}]
              (let [frozen (#'provider/capture-source capture)
                    name (module-name! (:module frozen)) path (:filename frozen)
                    _ (need (and (vector? dependencies) (<= (count dependencies) 16))
                            "Bounded explicit dependency vector required")
                    deps (mapv module-name! dependencies)
                    total (+ bytes (:byte-count frozen)) edge-count (+ edges (count deps))]
                (need (and (vector? dependencies) (<= (count deps) 16)
                           (= (count deps) (count (set deps)))) "Explicit unique direct dependencies required")
                (need (and (not= name exchange/prelude-name) (not (contains? seen name))
                           (not (contains? paths path))) "Duplicate/reserved project module or source path")
                (need (every? seen deps) "Dependencies must precede their dependent file")
                (need (and (<= total 524288) (<= edge-count 64)) "Aggregate project source/edge bound exceeded")
                {:files (conj files {:capture (select-keys capture [:text :path :module :sha256 :byte-count])
                                     :module name :dependencies deps})
                 :seen (conj seen name) :paths (conj paths path) :bytes total :edges edge-count}))
            {:files [] :seen #{} :paths #{} :bytes 0 :edges 0} entries)))
(defn- cell [project]
  (locking projects (or (.get projects project) (throw (ex-info "Actual issued Project required" {})))))
(defn- live! [holder]
  (let [s @holder]
    (need (and (= :open (:status s)) (identical? (:thread s) (Thread/currentThread)))
          "Project is terminal or belongs to another thread")
    (#'exchange/runtime! (:runtime-holder s)) s))
(defn open-project! [runtime entries]
  (let [files (plan-project entries) rh (#'exchange/issued @#'exchange/runtimes runtime)
        _ (#'exchange/runtime! rh) token (Project.)
        holder (atom {:status :open :thread (Thread/currentThread) :runtime runtime :runtime-holder rh
                      :files files :next-file 0 :modules {} :completed [] :active nil})]
    (locking projects (.put projects token holder)) token))
(defn inspect [project]
  (select-keys @(cell project) [:status :next-file :completed :stage :failure]))
(defn journal
  "Borrowed diagnostic aliases, including actual failed command/operation
   packets. This neither transfers guest credits nor authorizes retry."
  [project] @(cell project))
(defn- prepared-frontend! [bundle]
  (let [result (or (:setup-result bundle) (:setup bundle))
        original (:session result) actual (:frontend bundle)
        permitted [:runtime-step! :deadline-nanos :limits]
        protected (apply dissoc original permitted)]
    (need (and (= :prepared (:status result)) (map? original) (map? actual)
               (= (set (keys protected)) (set (keys (apply dissoc actual permitted))))
               (every? (fn [[key value]] (identical? value (get actual key))) protected)
               (fn? (:runtime-step! actual)) (integer? (:deadline-nanos actual)) (map? (:limits actual)))
          "Prepared frontend permits only explicit runtime/deadline/budget rewrapping")
    actual))
(defn- imported-scope! [s bundle parents]
  (let [child (:child bundle) adapter (get-in bundle [:admission :adapter]) r @(:runtime-holder s)
        driver (:driver child)]
    (need (and (identical? (:engine r) (:engine driver)) (identical? (:source r) (:source driver))
               (identical? (:current-ctx (:driver r)) (:current-ctx driver)))
          "Project bundle belongs to another runtime branch")
    (if (empty? parents)
      (do (need (and (nil? (:source-import bundle))
                     (identical? (:prelude-run r) (get-in adapter [:authority :finalized-run])))
                "Initial project file requires its actual fixed Prelude association")
          (batch/open-scope! driver adapter))
      (let [{:keys [finalized-run base]} (:source-import bundle)
            expected (into [exchange/prelude-name] (mapv #(exchange/with-module! % :module) parents))]
        (exchange/with-finalized! finalized-run
          (fn [run]
            (exchange/with-closure! (:closure run)
              (fn [view]
                (need (= expected (mapv :module (:requests view)))
                      "Prepared import closure differs from project direct dependencies")
                (let [selected (into {} (map (fn [token] [(exchange/with-module! token :module) token])
                                             (:module-roots view)))]
                  (doseq [[name parent] (map vector (rest expected) parents)]
                    (need (identical? parent (get selected name))
                          "Prepared import closure selected a different source module version")))))))
        (imports/open-generated-scope! child adapter base finalized-run)))))
(defn compile-next!
  "Compile/export one captured file on an ACTUALLY prepared bundle. Imported
   setup/Base/authority preparation is separate and uses issued source APIs.
   Holds genuine EOF until export, then retires EOF+adapter. Caller retains all
   original frontend setup owners and shared branch/runtime owners. No unwind."
  [project bundle {:keys [headers layout-directory quantum max-commands row-limit]
                   :or {quantum 1000 max-commands 128 row-limit 2048}}]
  (need (and (map? headers) (string? layout-directory) (seq layout-directory)
             (integer? quantum) (<= 100 quantum 10000)
             (integer? max-commands) (<= 1 max-commands 128)
             (integer? row-limit) (<= 1 row-limit 2048)) "Explicit bounded source/command policy required")
  (let [holder (cell project) s (live! holder)
        entry (get (:files s) (:next-file s))
        _ (need (and entry (nil? (:active s)) (not (:running? s))) "No next project file or another file is active")
        _ (prepared-frontend! bundle)
        parents (mapv #(get (:modules s) %) (:dependencies entry))
        capture (:capture entry)]
    ;; Publish every subsequent preparation/failure journal before its effects.
    (swap! holder assoc :running? true :active {:bundle bundle :entry entry :parents parents} :stage :scope-opening)
    (try
      (let [scope (imported-scope! s bundle parents)
            _ (swap! holder assoc-in [:active :scope] scope)
            _ (swap! holder assoc :stage :provider-opening)
            p (provider/open-provider! (:child bundle) (:frontend bundle) capture {:layout-directory layout-directory})
            _ (swap! holder assoc-in [:active :provider] p)
            captures (command/source-captures (get-in bundle [:child :code-receipt])
                       (assoc (provider/callbacks p) :headers headers))
            _ (swap! holder assoc-in [:active :captures] captures)]
        (loop [index 0 summaries []]
          (need (< index max-commands) "Project file reached command bound before genuine EOF")
          (swap! holder assoc :stage :command-opening)
          (let [frontend (options/rebase-idle-deadline (:frontend bundle))
                run (command/open-command! frontend (:admission bundle) captures
                      {:layout-directory layout-directory :quantum quantum :row-limit row-limit})
                _ (swap! holder assoc-in [:active :command-run] run)
                _ (swap! holder assoc :stage :command-running)
                result (command/run-command! run)
                _ (need (= :sealed (:status result)) "Project command failed; preserve actual Run journal")
                _ (swap! holder assoc-in [:active :receipt] (:receipt result))
                _ (swap! holder assoc :stage :code-preparing)
                prepared (batch/prepare-batch! scope (:receipt result))
                _ (swap! holder assoc-in [:active :pending-code] prepared)
                _ (need (contains? #{:empty :prepared} (:status prepared)) "Project command emitted unsupported code")
                linked (when (= :prepared (:status prepared)) (batch/link-batch! (:batch prepared)))
                _ (when linked (need (= :linked (:status linked)) "Project code did not link"))
                summary (:summary result) kind (:kind summary)
                summaries (conj summaries {:command summary :code (dissoc prepared :batch) :link linked})]
            (need (contains? #{:command :eoi} kind) "Project stopped without genuine EOF")
            (if (= :command kind)
              (do (command/rebase-idle-deadline! run 60000)
                  (need (= :retired (:status (command/retire! run))) "Command retirement did not complete")
                  (swap! holder update :active dissoc :command-run :receipt :pending-code)
                  (recur (inc index) summaries))
              (do
                (swap! holder assoc :stage :exporting)
                (let [module (exchange/export-module! (:runtime s) (:receipt result) scope parents)]
                  (swap! holder assoc-in [:active :module] module)
                  (exchange/with-module! module
                    (fn [view] (need (= (:module entry) (:module view)) "Exported module differs from captured project module")))
                  (swap! holder assoc :stage :file-retiring)
                  (let [retirement (exchange/retire-file! module run)]
                    (need (= :retired (:status retirement)) "Exported file retirement did not complete")
                    (provider/close! p) (batch/close! scope)
                    (swap! holder (fn [state]
                                    (-> state (update :next-file inc)
                                        (assoc-in [:modules (:module entry)] module)
                                        (update :completed conj {:module (:module entry) :commands summaries
                                                                 :retirement retirement :borrowed-frontend-bundle bundle})
                                        (assoc :active nil :stage :idle))))
                    {:status :exported :module module :summary (last (:completed @holder))})))))))
      (catch Throwable cause
        (swap! holder assoc :status :failed :failure (command/failure-summary cause))
        ;; Keep actual issuer capabilities, never the Throwable (whose ex-data
        ;; could retain this Project key through its own registry value).
        (when-let [operation (:operation (ex-data cause))]
          (let [op (#'exchange/issued @#'exchange/operations operation)]
            (need (identical? (:runtime-holder s) (:runtime-holder @op))
                  "Failure operation belongs to another project runtime")
            (swap! holder assoc-in [:active :exchange-operation] operation)))
        (throw (ex-info "Project file failed; preserve its actual resource journal" {:project project} cause)))
      (finally (swap! holder dissoc :running?)))))

(defn detach-journal!
  "Terminal host-custody handoff only. Returns all module capabilities and
   borrowed setup/failure journals and drops coordinator references. It performs
   no guest release, disposal, unwind, success certification or runtime reopen."
  [project]
  (let [holder (cell project) s @holder]
    (need (and (contains? #{:open :failed} (:status s))
               (identical? (:thread s) (Thread/currentThread)) (not (:running? s)))
          "Cannot detach a terminal, foreign-thread or running project")
    (reset! holder {:status :detached :thread (:thread s)})
    s))
