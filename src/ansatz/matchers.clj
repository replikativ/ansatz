(ns ansatz.matchers
  "Inherit Lean's matcher metadata (`Match.MatcherInfo`) into the env as a `:matcher-info`
   extension — the faithful basis for the `split` tactic on matchers (Lean's applyMatchSplitter,
   getEquationsFor). This metadata is NOT in the kernel export (lean4export emits only types +
   values); it is dumped separately by scripts/dump_matchers.lean from the SAME toolchain that
   produced the store (mirrors ansatz.attrs for @[simp]).

   Each entry (keyed by matcher name string) is a map:
     {:num-params N :num-discrs N :u-elim-pos (Option Nat) :discrs [hName?…]
      :overlaps [[from to]…] :alts [{:num-fields N :num-overlaps N :unit-thunk bool}…]}
   For NON-OVERLAPPING matchers (overlaps empty, every :num-overlaps 0 — ~91% of Init, incl. all
   the ones the wandler BYCASES cluster hits) the splitter is the matcher itself (Lean
   MatchEqs.lean:231-243); the overlapping ones carry full metadata for the deferred mkMatcher path."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.state :as state]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(defn- parse-info
  "Parse one NDJSON line into [name-string info-map], or nil."
  [line]
  (when (and line (not (str/blank? line)))
    (let [j (json/read-str line :key-fn keyword)]
      [(:name j)
       {:num-params (:numParams j)
        :num-discrs (:numDiscrs j)
        :u-elim-pos (:uElimPos j)                 ; nil = Prop-only
        :discrs (vec (:discrs j))                 ; hName? per discriminant (nil = no `h:`)
        :overlaps (mapv vec (:overlaps j))        ; [[overlapping overlapped]…]
        :alts (mapv (fn [a] {:num-fields (:numFields a)
                             :num-overlaps (:numOverlaps a)
                             :unit-thunk (:unitThunk a)})
                    (:alts j))}])))

(defn import-matchers
  "Return [env' stats]: `env` with matcher-info from `ndjson` (path or seq of lines) loaded into the
   `:matcher-info` extension (name→info map), keeping only matchers present as constants in `env`."
  [env ndjson]
  (let [lines (if (sequential? ndjson) ndjson (str/split-lines (slurp ndjson)))
        present? (fn [n] (some? (env/lookup env (name/from-string n))))]
    (reduce (fn [[e stats] line]
              (if-let [[nm info] (try (parse-info line) (catch Throwable _ nil))]
                (if (present? nm)
                  [(env/update-extension e :matcher-info {} assoc nm info)
                   (update stats :loaded (fnil inc 0))]
                  [e (update stats :skipped (fnil inc 0))])
                [e stats]))
            [env {}]
            lines)))

(defn import-matchers!
  "Load matcher-info from `ndjson` into the GLOBAL env (atomically). Returns the load stats."
  [ndjson]
  (let [stats (atom nil)]
    (swap! state/ansatz-env (fn [e] (let [[e' s] (import-matchers e ndjson)] (reset! stats s) e')))
    @stats))

(def ^:private bundled-resource "ansatz/init-matchers.ndjson.gz")

(defn load-bundled-matchers!
  "Import the bundled Init matcher-info corpus (gzipped NDJSON from scripts/dump_matchers.lean) into
   the GLOBAL env's :matcher-info extension. No-op if the resource isn't on the classpath."
  []
  (when-let [res (io/resource bundled-resource)]
    (let [lines (with-open [in (java.util.zip.GZIPInputStream. (.openStream res))]
                  (str/split-lines (slurp in)))]
      (import-matchers! lines))))

(defn matcher-info
  "Look up the MatcherInfo for matcher `nm` (string) in `env`'s :matcher-info extension, or nil."
  [env nm]
  (get (env/get-extension env :matcher-info {}) nm))

(defn non-overlapping?
  "True iff the matcher has no overlapping alternatives (splitter = matcher itself)."
  [info]
  (and info (empty? (:overlaps info)) (every? (comp zero? :num-overlaps) (:alts info))))
