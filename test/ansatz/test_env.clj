(ns ansatz.test-env
  "Shared immutable Init environments. Bundled Init is always available through
   the classpath resource API, with separate checked and TRUST replay delays.
   Full Init remains optional: prefer its local PSS store, then checked streaming
   replay of its NDJSON export."
  (:require [ansatz.export.parser :as parser]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.instance :as instance]
            [ansatz.export.replay :as replay]
            [ansatz.export.storage :as storage]
            [clojure.java.io :as io]))

(defn with-instance-registry
  "Attach Lean's bundled Init registry to a replayed Init test environment."
  [base]
  (env/with-extension base :instances
    (instance/load-bundled-instances
     {:present? #(some? (env/lookup base (name/from-string %)))})))

(defn- store-env [store-dir branch]
  (when (.exists (java.io.File. store-dir))
    (some-> (try (storage/load-env (storage/open-store store-dir) branch)
                 (catch Throwable _ nil))
            with-instance-registry)))

(defn ndjson-env
  "Stream an optional export into a test environment with the bundled instance registry."
  [f]
  (when (.exists (java.io.File. f))
    (with-instance-registry (:env (replay/replay-file-streaming f)))))

(def init-full-ndjson-env
  "Full Init streamed from the optional export, shared by tests exercising that fixture."
  (delay (ndjson-env "test-data/init.ndjson")))

(def init-full-env
  "Full Lean `Init` library. Prefers the PSS store, falls back to NDJSON. nil if
   neither is present."
  (delay (or (store-env "test-data/init-store" "init")
             @init-full-ndjson-env)))

(def bundled-init-text
  "Read the shipped Init closure through the classpath, independently of export size."
  (delay
    (let [res (io/resource "ansatz/init-medium.ndjson.gz")]
      (when-not res
        (throw (ex-info "bundled Init export missing from the classpath"
                        {:resource "ansatz/init-medium.ndjson.gz"})))
      (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
        (slurp in)))))

(defn- replay-bundled-init [verify?]
  (parser/with-parser-state
    (parser/parse-ndjson-string @bundled-init-text)
    (fn [parsed]
      (with-instance-registry
        (:env (replay/replay (:decls parsed) :verify? verify? :stop-on-error? true))))))

(def bundled-init-env
  "Shared bundled Init in TRUST mode, as used by core/load-init!. Never nil."
  (delay (replay-bundled-init false)))

(def checked-bundled-init-env
  "Shared bundled Init with checked replay. Admission failures propagate; never skips."
  (delay (replay-bundled-init true)))

(def init-medium-env
  "Compatibility name for the TRUST-mode bundled Init environment."
  bundled-init-env)
