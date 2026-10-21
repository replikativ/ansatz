(ns prototype.resident-init-prefix
  "Optional checked-Init prefix preparation, not an over-Init source loader.
   The original successful CHECKED result is a TRUSTED host input. Issuing an
   opaque prefix does not authenticate the provenance of a caller-created map.
   Context branches own guest roots; native Stores and catalogues stay borrowed."
  (:require [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.module-import :as imports]
            [prototype.module-store :as store]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m])
  (:import [ansatz.kernel Env ConstantInfo]
           [java.util WeakHashMap]))

(deftype InitPrefix [])
(defonce ^:private issued (WeakHashMap.))
(defn- fail [message data] (throw (ex-info message data)))
(defn- capability! [value]
  (or (locking issued (.get issued value))
      (fail "Expected an issued resident Init prefix" {})))

(def preparation-roots
  "Fixed sequential native assembly and future hybrid/finalizer/checking roots.
   All must match independently captured preparation before any guest call."
  (vec (distinct (concat (vals imports/helpers) (vals source/helpers)
                         [source/hybrid-assemble-helper]))))

(defn- preparation-readiness!
  "Host-only checks. CONFIGURATION and NATIVE-BINDINGS are independently captured
   trusted host inputs. Routing must already be prepared: this API changes no
   binding. Only read/free/evalConst may differ from the original native registry;
   in particular the original native initializer callback is preserved exactly."
  [prepared configuration native-bindings]
  (resident/adoption-readiness! prepared configuration)
  (eval/validate-executables! (:world prepared) (:trusted-functions configuration) preparation-roots)
  ;; This public constructor validates required native signatures and handlers.
  ;; Its fresh closures are discarded; installed closures are authenticated by
  ;; the independent configuration, not by equality with a newly built registry.
  (source/make-hybrid-bindings native-bindings)
  (let [actual (get-in prepared [:session :bindings])
        replaced #{"lean_compacted_region_read" "lean_compacted_region_free" "lean_eval_const"}]
    (when-not (= (set (keys actual)) (set (keys native-bindings)))
      (fail "Init prefix native and prepared binding registries differ" {}))
    (doseq [[symbol binding] native-bindings :when (not (contains? replaced symbol))]
      (when-not (identical? binding (get actual symbol))
        (fail "Init prefix native capability changed" {:symbol symbol})))
    (doseq [symbol ["lean_compacted_region_read" "lean_compacted_region_free"]]
      (when-not (and (= (:signature (get native-bindings symbol)) (:signature (get actual symbol)))
                     (fn? (:handler (get actual symbol))))
        (fail "Init prefix hybrid routing signature changed" {:symbol symbol}))))
  true)

(defn- checked! [entry checked]
  (let [world (:world entry) original (:world checked) certificate (:certificate checked)
        ^Env env (:env certificate) sources (:projection-sources certificate)
        constants (:constants certificate) projected (:projected certificate)]
    (when-not (and (= :ok (:status checked)) (= (:environment entry) (:environment checked))
                   (map? original) (instance? Env env) (map? constants) (map? projected)
                   (= (set (keys constants)) (set (keys projected)))
                   (= 1 (count sources)) (= 1 (count (:native-imports world)))
                   (identical? (first sources) (first (:native-imports world)))
                   (= 1 (count (:native-imports original)))
                   (identical? (first sources) (first (:native-imports original))))
      (fail "Init prefix requires the original checked result and exact attached Source" {}))
    (let [actual (.allConstants env)]
      (when-not (and (= (count actual) (count projected))
                     (every? (fn [^ConstantInfo ci] (identical? ci (get projected (.name ci)))) actual))
        (fail "Init prefix checked ConstantInfo identities differ" {})))
    (doseq [[_ value] constants]
      (when-not (and (m/ref? value)
                     (or (m/native-reference? world value)
                         (let [before (get-in original [:heap (:id value)])
                               after (get-in world [:heap (:id value)])]
                           (and before after (= (dissoc before :rc) (dissoc after :rc))))))
        (fail "Init prefix checked guest constant changed" {})))
    certificate))

(defn- packet [entry world session]
  ;; A new Context does not carry a checking certificate in evolving metadata.
  {:world world :session session :environment (:environment entry)
   :options (:options entry) :catalogue (:catalogue entry)})

(defn prepare-init-prefix
  "Prepare a checked native Init prefix in a NEW persistent resident branch.
   CHECKED must be the original successful checking result for this Context's
   Environment, supplied by trusted host code. OPTIONS is exactly
   {:configuration independent-resident-config :native-bindings original-native}.
   No source reopening/bootstrap, initializer replay or binding replacement.
   Return {:context new-context :prefix issued-capability :receipt descriptive-data}.

   The world registry owns the prefix state; the capability borrows it and keeps
   the original certificate privately. Env/Options ownership follows resident/fork:
   the new branch inherits its existing owners without retain/drop churn. Input
   remains unchanged/open. Failure retains terminal exact packets, not a retry or
   cleanup capability; the borrowed Store/lease must outlive retained branches."
  [context checked {:keys [configuration native-bindings] :as options}]
  (locking context
    (let [entry (resident/snapshot context) active (atom (:session entry))
          progress (volatile! (:world entry)) phase (volatile! :entry)
          prepared (volatile! nil) last-call (volatile! nil)
          invoke (fn [world target args]
                   (vreset! progress world)
                   (let [called (raw/call @active world target args)]
                     (vreset! last-call {:target target :arguments args :returned called})
                     (reset! active (:session called)) (vreset! progress (:state called))
                     [(:state called) (:value called)]))]
      (try
        (when-not (and (map? options) (= #{:configuration :native-bindings} (set (keys options)))
                       (map? configuration) (map? native-bindings))
          (fail "Init prefix requires explicit independent configuration and original native bindings" {}))
        (preparation-readiness! entry configuration native-bindings)
        (let [certificate (checked! entry checked)
              loaded (store/describe-attached @progress (first (:projection-sources certificate)))]
          (vreset! phase :prepare-started)
          (let [result (source/prepare-init-prefix loaded invoke checked)]
            (vreset! prepared result) (vreset! progress (:world result))
            (vreset! phase :adopt-started)
            (let [next-context (resident/adopt-prepared (packet entry @progress @active) configuration)
                  prefix (InitPrefix.)
                  receipt {:module-count (count (get-in result [:prefix :modules]))
                           :constant-count (count (:constants certificate))
                           :producer-imports (get-in result [:prefix :producer-imports])}]
              (locking issued
                (.put issued prefix {:prefix (:prefix result) :certificate certificate
                                     :configuration configuration :native-bindings native-bindings
                                     :receipt receipt}))
              {:context next-context :prefix prefix :receipt receipt})))
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Resident Init prefix preparation failed")
                          (merge {:checkpoint @progress :checkpoint-session @active} (ex-data cause)
                                 {:resident-init-prefix-entry entry :resident-init-prefix-checked checked
                                  :resident-init-prefix-preparation @prepared :resident-init-prefix-last-call @last-call
                                  :resident-init-prefix-phase @phase :resident-init-prefix-terminal? true
                                  :resident-init-prefix-root-ownership :inherited-in-independent-branch}) cause)))))))

(defn descriptor
  "Borrow a descriptive receipt; it grants no checking or replay authority."
  [prefix] (:receipt (capability! prefix)))

(defn release-prefix
  "Remove an issued prefix's registry owner in a NEW branch and adopt its roots.
   Public lower release validates exact registry/scaffold/anchor/open Source before
   releasing once. Input and inherited forks retain their registry owner. Closing
   a Context does not release this registry owner or close the borrowed Source."
  [context prefix]
  (locking context
    (let [entry (resident/snapshot context) progress (volatile! (:world entry))
          phase (volatile! :entry) released (volatile! nil)]
      (try
        (let [{raw-prefix :prefix :keys [certificate configuration native-bindings]} (capability! prefix)]
          (preparation-readiness! entry configuration native-bindings)
          (when-not (and (identical? raw-prefix (get-in @progress [:source-import-prefixes (:id (:state raw-prefix))]))
                         (identical? (:env certificate) (:checked-env raw-prefix)))
            (fail "Issued Init prefix is absent or belongs to another branch" {}))
          (vreset! phase :release-started)
          (vreset! progress (source/release-init-prefix @progress raw-prefix))
          (vreset! released (packet entry @progress (:session entry)))
          (vreset! phase :adopt-started)
          {:context (resident/adopt-prepared @released configuration) :receipt (:receipt (capability! prefix))})
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Resident Init prefix release failed")
                          (merge {:checkpoint @progress :checkpoint-session (:session entry)} (ex-data cause)
                                 {:resident-init-prefix-entry entry :resident-init-prefix-released @released
                                  :resident-init-prefix-phase @phase :resident-init-prefix-terminal? true
                                  :resident-init-prefix-root-ownership :inherited-in-independent-branch}) cause)))))))
