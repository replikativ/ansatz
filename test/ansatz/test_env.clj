(ns ansatz.test-env
  "Shared, lazily-loaded kernel environments for tests.

   Loading Init is expensive and several namespaces need it, so each source is
   loaded at most ONCE per test run via these delays. Two fast paths, in order
   of preference:

   1. A prebuilt PSS store (test-data/init-store) — opened lazily with on-demand
      declaration loading; ~40ms to a usable env. Build it once with:

        clj -J-Xmx10g -M -e '(require (quote [ansatz.export.storage :as s]))
          (let [sm (s/open-store \"test-data/init-store\")]
            (s/import-ndjson-streaming! sm \"test-data/init.ndjson\" \"init\"))'

      The store is gitignored (large, not shipped yet).

   2. Fallback: replay the NDJSON in TRUST mode (`:verify? false`) — tests use
      Init, they don't validate the export, so admit without re-typechecking
      (~125× faster than verifying). Used when the store is absent (e.g. CI).

   The returned Env is immutable, so tests freely build on it; nil if neither the
   store nor the NDJSON is present, so integration tests skip.

   `bundled-init-env` is different in kind and is what most tests should use: it is
   the store ansatz SHIPS (resources/ansatz/init-medium.ndjson.gz, on the classpath),
   so it is always available — no test-data fixture, and identical in CI and on a
   developer box. The `test-data/*` fixtures above are whatever that machine happens
   to have lying around, which is how the omega suite spent a release asserting
   against a stale 2997-declaration slice."
  (:require [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.export.storage :as storage]
            [clojure.java.io :as io]))

(defn- store-env [store-dir branch]
  (when (.exists (java.io.File. store-dir))
    (try (storage/load-env (storage/open-store store-dir) branch)
         (catch Throwable _ nil))))

(defn- ndjson-env [f]
  (when (.exists (java.io.File. f))
    (:env (replay/replay (:decls (parser/parse-ndjson-file f)) :verify? false))))

(def init-full-env
  "Full Lean `Init` library. Prefers the PSS store, falls back to NDJSON. nil if
   neither is present."
  (delay (or (store-env "test-data/init-store" "init")
             (ndjson-env "test-data/init.ndjson"))))

(def init-medium-env
  "Medium Init slice from `test-data/`. nil if that fixture is absent — which it is on
   CI and on a fresh clone. Prefer `bundled-init-env`."
  (delay (or (store-env "test-data/init-medium-store" "init")
             (ndjson-env "test-data/init-medium.ndjson"))))

(def bundled-init-env
  "The Init tier ansatz ships in the jar: `resources/ansatz/init-medium.ndjson.gz`,
   the transitive dependency closure of `scripts/init-store-roots.txt`, replayed in
   TRUST mode. This is exactly the environment `ansatz.core/load-init!` gives a
   library user, so a tactic that works here works out of the box.

   Never nil: the resource is on the classpath by construction. Loaded once."
  (delay
    (let [res (io/resource "ansatz/init-medium.ndjson.gz")]
      (when-not res
        (throw (ex-info "bundled Init export missing from the classpath"
                        {:resource "ansatz/init-medium.ndjson.gz"})))
      (let [ndjson (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
                     (slurp in))]
        (:env (replay/replay (:decls (parser/parse-ndjson-string ndjson)) :verify? false))))))
