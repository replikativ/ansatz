(ns ansatz.export.facts
  "FACTS about declarations, computed at import by walking the RAW expression records — no
   Expr objects are built, which is why this is cheap (median 7 ms per declaration on Mathlib
   for the whole proof DAG; building the statement's Expr alone costs 35 ms).

   Per declaration: :kind, :num-univs, :num-binders (the ∀-telescope), :concl-head (the head
   constant of the conclusion), :type-id/:value-id into the term store, :mentions (constants of
   the STATEMENT) and :depends-on (constants of the VALUE — the proof or body). Mentions and
   dependencies are name-ids here; the catalogue resolves them to entities.

   Raw record layout (ansatz.kernel.ExprStore): tag byte, then
     CONST  name-id(4) …            APP  fn-id(4) arg-id(4)
     LAM/FORALL binder(1) name-id(4) type-id(4) body-id(4)
     LET    name-id(4) type-id(4) value-id(4) body-id(4)
     MDATA  expr-id(4)              PROJ name-id(4) index(4) expr-id(4)"
  (:require [ansatz.export.storage :as storage]
            [ansatz.kernel.name :as nm]
            [org.replikativ.persistent-sorted-set :as pss]
            [konserve.core :as k])
  (:import [ansatz.export.types CIShell]
           [java.util BitSet HashSet]
           [java.util.concurrent ConcurrentHashMap]))

(def ^:private kinds [:axiom :def :thm :opaque :quot :induct :ctor :rec])

(defn- u32 ^long [^bytes b ^long o]
  (bit-or (bit-shift-left (bit-and (aget b o) 0xff) 24)
          (bit-shift-left (bit-and (aget b (+ o 1)) 0xff) 16)
          (bit-shift-left (bit-and (aget b (+ o 2)) 0xff) 8)
          (bit-and (aget b (+ o 3)) 0xff)))

(defn worker-context
  "Per-worker handles over a branch: the env and exprs trees and a name-id → string resolver
   backed by the SHARED `name-cache` (a ConcurrentHashMap; PSS reads are thread-safe, the
   resolver caches are not — hence one context per worker)."
  [store-map branch-name ^ConcurrentHashMap name-cache]
  (let [{:keys [storage store]} store-map
        meta (k/get store [:branches branch-name] nil {:sync? true})
        names-pss (pss/restore-by storage/id-cmp (:names-root meta) storage)]
    {:env-pss (pss/restore-by storage/name-cmp (:env-root meta) storage)
     :exprs-pss (pss/restore-by storage/id-cmp (:exprs-root meta) storage)
     :name-of (fn [^long id]
                (or (.get name-cache id)
                    (let [s (nm/->string (nth (pss/lookup names-pss [id nil]) 1))]
                      (.put name-cache id s)
                      s)))}))

(defn- raw [{:keys [exprs-pss]} ^long id]
  (nth (pss/lookup exprs-pss [id nil]) 1))

(defn reachable-consts
  "The name-ids of every CONST reachable from expression `root` (a vector, insertion order)."
  [ctx ^long root]
  (let [seen (BitSet.) acc (HashSet.) out (transient [])]
    (loop [todo (list root)]
      (when-let [id (first todo)]
        (let [r (rest todo) id (long id)]
          (if (.get seen (int id))
            (recur r)
            (do (.set seen (int id))
                (let [^bytes b (raw ctx id) tag (int (aget b 0))]
                  (case tag
                    2 (let [n (u32 b 1)] (when (.add acc n) (conj! out n)) (recur r))
                    3 (recur (conj r (u32 b 1) (u32 b 5)))
                    (4 5) (recur (conj r (u32 b 6) (u32 b 10)))
                    6 (recur (conj r (u32 b 5) (u32 b 9) (u32 b 13)))
                    9 (recur (conj r (u32 b 1)))
                    10 (recur (conj r (u32 b 9)))
                    (recur r))))))))
    (persistent! out)))

(defn telescope+head
  "[num-binders head-name-id] of a type: the length of its leading ∀-telescope and the head
   constant of the conclusion (nil when the head is not a constant — a sort, a variable)."
  [ctx ^long type-id]
  (loop [id type-id n 0]
    (let [^bytes b (raw ctx id) tag (int (aget b 0))]
      (case tag
        5 (recur (u32 b 10) (inc n))                          ; FORALL: body
        9 (recur (u32 b 1) n)                                 ; MDATA: inner
        (do (loop [hid id]                                    ; conclusion: app spine head
              (let [^bytes hb (raw ctx hid) htag (int (aget hb 0))]
                (case htag
                  3 (recur (u32 hb 1))
                  9 (recur (u32 hb 1))
                  2 [n (u32 hb 1)]
                  [n nil]))))))))

(defn decl-facts
  "The facts of declaration `name-str`, or nil when it is not in the branch."
  [{:keys [env-pss] :as ctx} name-str]
  (when-let [entry (pss/lookup env-pss [(nm/from-string name-str) nil])]
    (let [m (.data ^CIShell (nth entry 1))
          type-id (long (:type-id m))
          value-id (:value-id m)
          [nb head] (telescope+head ctx type-id)]
      (cond-> {:name name-str
               :kind (nth kinds (int (:tag m)))
               ;; longs, not ints: datahike's :db.type/long validation is by class
               :num-univs (long (count (:lps m)))
               :num-binders (long nb)
               :type-id type-id
               :mentions (reachable-consts ctx type-id)}
        head (assoc :concl-head head)
        value-id (assoc :value-id (long value-id)
                        :depends-on (reachable-consts ctx (long value-id)))))))

(defn resolve-names
  "A facts map with its name-ids turned into strings (through the worker's resolver)."
  [{:keys [name-of]} f]
  (cond-> (update f :mentions #(mapv name-of %))
    (:concl-head f) (update :concl-head name-of)
    (:depends-on f) (update :depends-on #(mapv name-of %))))

(defn facts-for
  "Facts, names resolved, for `names` — one worker's share. `name-cache` is shared across
   workers."
  [store-map branch-name name-cache names]
  (let [ctx (worker-context store-map branch-name name-cache)]
    (into [] (keep (fn [n] (some->> (decl-facts ctx n) (resolve-names ctx)))) names)))

(defn read-modules-file
  "scripts/dump_modules.lean output (.ndjson or .ndjson.gz) → {name-str {:module s :doc s}}.
   nil when the file does not exist."
  [path]
  (let [f (clojure.java.io/file path)]
    (when (.exists f)
      (let [in (clojure.java.io/input-stream f)
            in (if (.endsWith (.getName f) ".gz") (java.util.zip.GZIPInputStream. in) in)
            read-json (requiring-resolve 'clojure.data.json/read-str)]
        (with-open [r (clojure.java.io/reader in)]
          (into {}
                (keep (fn [line]
                        (let [m (read-json line :key-fn keyword)]
                          (when (:name m)
                            [(:name m) (cond-> {:module (:module m)} (:doc m) (assoc :doc (:doc m)))]))))
                (line-seq r)))))))
