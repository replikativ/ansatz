(ns prototype.bootstrap
  "Native Lean elaboration bootstrap for the experimental JVM runtime.
  This does NOT host Lean's frontend. Optional kernel export is checked by Ansatz."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [prototype.import-ir :as ir]
            [prototype.interop :as interop]
            [ansatz.export.replay :as replay]))

(def toolchain "+leanprover/lean4:v4.33.1")
(defn- command! [stage args env]
  (let [result (apply shell/sh (concat args [:env env]))]
    (when-not (zero? (:exit result))
      (throw (ex-info "Native Lean bootstrap command failed" (assoc result :stage stage :argv args))))
    (:out result)))

(defn load-file!
  "Compile a Lean module natively and execute its selected IR on the JVM.
  :module names the source relative to :source-root (default lean); dependencies
  must already be compiled or installed. roots are explicit Lean entry names.
  :kernel-exporter optionally names a matching lean4export executable. Strict
  kernel checking must succeed before returning a linked session. No global
  Ansatz context is changed. Host implementations remain trusted bindings."
  [{:keys [module roots bindings source-root build-root kernel-exporter backend code-cache]
    :or {source-root "lean" build-root "target/bootstrap" backend :jvm}}]
  (when-not (and (string? module) (re-matches #"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*" module)
                 (seq roots) (every? string? roots))
    (throw (ex-info "Bootstrap requires module and explicit roots" {:module module :roots roots})))
  (let [build (.getCanonicalPath (io/file build-root))
        source (.getCanonicalPath (io/file source-root))
        relative (str/replace module "." "/")
        input (str (io/file source (str relative ".lean")))
        olean (io/file build (str relative ".olean"))
        jsonl (io/file build (str relative ".jsonl"))
        inherited (into {} (System/getenv))
        prefix (str/trim (command! :toolchain ["lean" toolchain "--print-prefix"] inherited))
        env (assoc inherited "LEAN_SYSROOT" prefix "LEAN_PATH"
                   (str build (when-let [old (get inherited "LEAN_PATH")]
                                (str java.io.File/pathSeparator old))))]
    (io/make-parents olean)
    (command! :compile ["lean" toolchain (str "--root=" source) "-o" (str olean) input] env)
    (spit jsonl (command! :ir-export (into ["lean" toolchain "--run" "lean/Export.lean" "--closure" module] roots) env))
    (let [checked
          (when kernel-exporter
            (let [output (str (io/file build (str relative ".ndjson")))
                  _ (spit output (command! :kernel-export (into [kernel-exporter module "--"] roots) env))
                  checked (replay/replay-file-streaming output)]
              (when (pos? (get-in checked [:stats :errors]))
                (throw (ex-info "Ansatz rejected bootstrap declarations"
                                (select-keys checked [:stats :error-names]))))
              checked))
          catalogue (ir/index-bundles [jsonl])
          names (mapv (fn [label]
                        (let [found (filter #(= label (ir/name-label %)) (keys (:declarations catalogue)))]
                          (when-not (= 1 (count found)) (throw (ex-info "Missing or ambiguous export root" {:name label})))
                          (first found))) roots)]
      (assoc (if code-cache (interop/open-session catalogue names bindings backend code-cache)
                           (interop/open-session catalogue names bindings backend))
             :frontend :native-bootstrap :kernel-status (if checked :checked :unchecked)
             :kernel-env (:env checked) :kernel-stats (:stats checked)
             :module module :source input :ir-path (str jsonl)))))
