(ns prototype.bootstrap
  "Native Lean elaboration bootstrap for the experimental JVM runtime.
  This does NOT host Lean's frontend. Optional kernel export is checked by Ansatz."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [prototype.import-ir :as ir]
            [prototype.interop :as interop]
            [prototype.initialization :as initialization]
            [prototype.module-runtime :as modules]
            [prototype.declaration-store :as store]
            [prototype.runtime-abi :as abi]
            [prototype.entropy :as entropy]
            [prototype.machine :as m]
            [prototype.lazy-runtime :as lazy]
            [ansatz.export.replay :as replay]))

(def toolchain "+leanprover/lean4:v4.33.1")
(defn- command! [stage args env]
  (let [result (apply shell/sh (concat args [:env env]))]
    (when-not (zero? (:exit result))
      (throw (ex-info "Native Lean bootstrap command failed" (assoc result :stage stage :argv args))))
    (:out result)))

(defn- entropy-input [options]
  (let [provided? (contains? options :entropy)
        tape (if provided? (:entropy options)
               (let [bytes (byte-array 1024)]
                 (.nextBytes (java.security.SecureRandom.) bytes)
                 {:bytes (mapv #(bit-and 255 %) bytes) :position 0}))
        tape (:entropy (first (entropy/take-bytes {:entropy tape} 0)))]
    (doseq [byte (:bytes tape)]
      (when-not (and (integer? byte) (<= 0 byte 255))
        (m/fail "Invalid guest entropy byte" {:value byte})))
    {:tape tape :metadata {:source (if provided? :provided :host-secure-random)
                          :capacity (count (:bytes tape)) :initial-position (:position tape)
                          :forks :replay}}))

(defn- module-plan! [catalogue module]
  (let [plans (vec (keep :initializationPlan (:manifests catalogue)))]
    (when-not (and (= 1 (count plans)) (vector? (:module (first plans)))
                   (= module (ir/name-label (:module (first plans)))))
      (m/fail "Source export must provide the file's own producer initialization plan" {:module module}))
    (first plans)))

(defn- environment-input [options inherited]
  (let [environment (if (contains? options :environment) (:environment options) inherited)]
    (when-not (and (map? environment) (every? (fn [[k v]] (and (string? k) (string? v))) environment))
      (m/fail "Guest environment must map strings to strings" {}))
    (into {} environment)))

(defn- module-lowerer [catalogue bindings]
  (fn [row]
    (let [ext (get-in row [:ir :extern]) symbol (when ext (abi/symbol-for ext))]
      (if (and symbol (contains? bindings symbol))
        (interop/lower bindings row)
        (abi/lower-deferred-catalogue catalogue row)))))

(defn load-file!
  "Compile a Lean module natively and execute its selected IR on the JVM.
  :module names the source relative to :source-root (default lean); dependencies
  must already be compiled or installed. roots are explicit Lean entry names.
  :kernel-exporter optionally names a matching lean4export executable. Strict
  kernel checking must succeed before returning a linked session. No global
  Ansatz context is changed. Host implementations remain trusted bindings.
  :initialize-imports true requires :import-catalogue with producer-time plans
  for every transitive import (raw or indexed). It exports this file's IR, plan
  and olean in one native frontend invocation, overlays the catalogue and runs
  the complete ordered module plan. This path exports source-local declarations
  only; imported bodies come from their producer catalogue. Missing plans/actually reached extern traps
  fail explicitly. :initialize-locals retains its existing local-only behavior.
  :entropy supplies a replayable {:bytes vector :position n} input; otherwise
  the host supplies 1024 SecureRandom bytes once before guest execution. Session
  calls fork the resulting :initial-world and replay its remaining input.
  :environment overrides the immutable guest environment snapshot; by default
  it snapshots System/getenv. :environment-input metadata records :snapshot.
  Imported initialization accepts :initialization-fuel, :checkpoint and
  :checkpoint-every; failures expose clean module checkpoints for explicit resume."
  [{:keys [module roots bindings source-root build-root kernel-exporter backend code-cache initialize-locals
           initialize-imports import-catalogue initialization-fuel checkpoint checkpoint-every]
    :or {source-root "lean" build-root "target/bootstrap" backend :jvm} :as options}]
  (when-not (and (string? module) (re-matches #"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*" module)
                 (seq roots) (every? string? roots))
    (throw (ex-info "Bootstrap requires module and explicit roots" {:module module :roots roots})))
  (when (and initialize-imports
             (not (and (map? import-catalogue) (map? (:declarations import-catalogue))
                       (sequential? (:manifests import-catalogue)))))
    (m/fail "Imported initialization requires an import-catalogue with producer module plans" {}))
  (let [build (.getCanonicalPath (io/file build-root))
        source (.getCanonicalPath (io/file source-root))
        relative (str/replace module "." "/")
        input (str (io/file source (str relative ".lean")))
        olean (io/file build (str relative ".olean"))
        jsonl (io/file build (str relative ".jsonl"))
        inherited (into {} (System/getenv))
        prefix (str/trim (command! :toolchain ["lean" toolchain "--print-prefix"] inherited))
        source-time? (or initialize-locals initialize-imports)
        env (assoc inherited "LEAN_SYSROOT" prefix "LEAN_PATH"
                   (str build (when-let [old (get inherited "LEAN_PATH")]
                                (str java.io.File/pathSeparator old))))]
    (io/make-parents olean)
    (when-not source-time?
      (command! :compile ["lean" toolchain (str "--root=" source) "-o" (str olean) input] env))
    (spit jsonl (command! :ir-export (into (if source-time?
                                      ["lean" toolchain "--run" "lean/Export.lean" "--source" input "--olean" (str olean)
                                       (if initialize-imports "--local" "--closure") module]
                                      ["lean" toolchain "--run" "lean/Export.lean" "--closure" module]) roots) env))
    (let [checked
          (when kernel-exporter
            (let [output (str (io/file build (str relative ".ndjson")))
                  _ (spit output (command! :kernel-export (into [kernel-exporter module "--"] roots) env))
                  checked (replay/replay-file-streaming output)]
              (when (pos? (get-in checked [:stats :errors]))
                (throw (ex-info "Ansatz rejected bootstrap declarations"
                                (select-keys checked [:stats :error-names]))))
              checked))
          file-catalogue (ir/index-bundles [jsonl])
          file-plan (when initialize-imports (module-plan! file-catalogue module))
          catalogue (if initialize-imports (store/overlay import-catalogue file-catalogue) file-catalogue)
          names (mapv (fn [label]
                        (let [found (filter #(= label (ir/name-label %)) (keys (:declarations catalogue)))]
                          (when-not (= 1 (count found)) (throw (ex-info "Missing or ambiguous export root" {:name label})))
                          (first found))) roots)]
      (let [linked (cond initialize-imports
                         (modules/link catalogue (:module file-plan) names {:lower (module-lowerer catalogue bindings)})
                         initialize-locals
                         (initialization/link-local-plan catalogue names #(interop/lower bindings %)))
            session (if linked
                      (interop/open-functions (:functions linked) bindings backend (or code-cache (lazy/code-cache)))
                      (if code-cache (interop/open-session catalogue names bindings backend code-cache)
                           (interop/open-session catalogue names bindings backend)))
            entropy (entropy-input options)
            initial (assoc (m/world (:functions session)) :entropy (:tape entropy)
                           :environment (environment-input options inherited))
            fuel (or initialization-fuel (:fuel session))
            initial-world (cond initialize-imports
                                (modules/run linked initial backend fuel
                                             (cond-> {:code-cache (or code-cache (get-in session [:program :cache]))}
                                               checkpoint (assoc :checkpoint checkpoint)
                                               checkpoint-every (assoc :checkpoint-every checkpoint-every)))
                                initialize-locals
                                (initialization/run-local-plan linked initial backend fuel)
                                :else initial)]
      (cond-> (assoc session
             :frontend :native-bootstrap :kernel-status (if checked :checked :unchecked)
             :kernel-env (:env checked) :kernel-stats (:stats checked)
             :module module :source input :ir-path (str jsonl)
             :initial-world initial-world :entropy-input (:metadata entropy) :environment-input :snapshot)
        linked (assoc :initialization-plan (:plan linked) :initialization (if initialize-imports :imports :local))
        initialize-imports (assoc :module-initialization (:expanded linked)
                                 :module-plans (:module-plans linked)))))))
