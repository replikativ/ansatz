(ns native-typed-bridge-probe-v1
  "Fixed native evidence bridge execution. No module startup or public Project."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [clojure.string :as str] [java-ir-baseline :as j])
  (:import [java.nio.file Files LinkOption] [java.nio.charset StandardCharsets]
           [java.math BigInteger] [java.security MessageDigest] [java.util WeakHashMap]))
(deftype Session [])
(defonce ^:private sessions (WeakHashMap.))
(def ^:private pins
  {"positive.stdout" "6e2456457ae4539901f3c2ad0584fac7637178f2503f01f2f5ecbc25be37164c"
   "imported.stdout" "3e75d8594bed682b1c4277ee17c8f8791a249a1b0306e560d6fafd85f9d221d0"
   "source-export-NativeEntryCases.stdout" "e825fc6d6ace317b86a006c9df90c9a716dc7d236913091e214bbec5ec82914c"
   "source-export-NativeEntryImported.stdout" "2c0582675c30773ba465041c4bb1cb8937f378ec52f92e9842af02227d837780"})
(defn- need [p message] (when-not p (throw (ex-info message {:profile :native-typed-bridge-v1}))))
(defn- sha [b] (apply str (map #(format "%02x" (bit-and 255 %))
  (.digest (MessageDigest/getInstance "SHA-256") ^bytes b))))
(defn- field [o k] (let [f (.getDeclaredField (class o) k)] (.setAccessible f true) (.get f o)))
(defn entry-name [module leaf] ["str" ["str" ["anonymous"] module] leaf])
(defn- label [n]
  (loop [n n out () depth 0]
    (need (< depth 128) "Name depth bound")
    (if (= ["anonymous"] n) (str/join "." out)
      (do (need (and (vector? n) (= 3 (count n)) (#{"str" "num"} (first n))
                     (string? (nth n 2)) (<= (count (nth n 2)) 4096)) "Malformed typed Name")
          (when (= "num" (first n))
            (let [s (nth n 2)]
              (need (and (re-matches #"0|[1-9][0-9]{0,19}" s)
                         (<= (BigInteger. s) (BigInteger. "18446744073709551615"))) "Invalid numeric Name")))
          (recur (second n) (conj out (nth n 2)) (inc depth))))))
(defn- read-fixed! [directory file]
  (let [p (.toPath (io/file (str directory) file))]
    (need (and (Files/isRegularFile p (into-array LinkOption [LinkOption/NOFOLLOW_LINKS]))
               (<= (Files/size p) 1048576)) "Bounded original evidence file required")
    (let [b (Files/readAllBytes p) s (String. b StandardCharsets/UTF_8)]
      (need (and (<= (alength b) 1048576) (= (pins file) (sha b))) "Frozen native evidence pin differs")
      s)))
(defn- abi [row]
  (let [decl (or (get-in row ["ir" "fdecl"]) (get-in row ["ir" "extern"]))]
    {"name" (get decl "f") "xs" (get decl "xs") "type" (get decl "type")}))
(defn- merge-exact [index row]
  (let [n (get row "name")]
    (label n)
    (need (= "decl" (get row "kind")) "Nondeclaration evidence row")
    (when-let [old (get index n)] (need (= old row) "Conflicting evidence rows"))
    (assoc index n row)))
(defn- pure-row! [row]
  (need (and (contains? #{"ordinary" "value" "closed" "ground"} (get-in row ["runtime" "role"]))
             (nil? (get-in row ["runtime" "initializer"]))
             (nil? (get-in row ["runtime" "initializationAction"])) (nil? (get row "redirect")))
        "Initializer/redirect-dependent row is outside bridge profile")
  (need (not-any? #(and (map? %) (contains? % "ap"))
                 (tree-seq coll? seq (get row "ir"))) "Dynamic application is outside selected pure closure")
  row)
(defn- expected-type! [signature actual]
  (let [base (if (= signature "nat-to-nat") "Nat" "String")
        constant ["const" ["str" ["anonymous"] base] []]]
    (need (and (vector? actual) (= 5 (count actual)) (= "forall" (first actual))
               (= "default" (nth actual 2)) (= constant (nth actual 3)) (= constant (nth actual 4)))
          "Actual native DefEq template differs from requested signature")))
(defn- closure [index roots]
  (loop [pending (vec roots) seen #{}]
    (need (<= (count pending) 4096) "Static work bound")
    (if-let [n (peek pending)]
      (if (seen n) (recur (pop pending) seen)
        (let [row (get index n)]
          (need row "Missing static dependency") (pure-row! row)
          (need (< (count seen) 256) "Selected static closure bound")
          (recur (into (pop pending) (get row "dependencies")) (conj seen n))))
      (select-keys index seen))))
(defn- metadata! [documents source-rows]
  (let [index (reduce merge-exact {} (mapcat #(get % "declarations") documents))
        entries (reduce (fn [out e]
                          (let [n (get e "name") signature (get-in e ["typeCheck" "signature"])]
                            (if (= "io-unit" signature) out
                              (do
                                (need (and (#{"nat-to-nat" "string-to-string"} signature)
                                           (= "definition" (get e "kind")) (= [] (get e "levelParams"))
                                           (= "Lean.Meta.isDefEq" (get-in e ["typeCheck" "algorithm"]))
                                           (= "default" (get-in e ["typeCheck" "transparency"]))
                                           (vector? (get e "actualType")) (vector? (get-in e ["typeCheck" "expectedType"])))
                                      "Unknown actual entry type/check profile")
                                (expected-type! signature (get-in e ["typeCheck" "expectedType"]))
                                (doseq [role ["raw" "callable"]]
                                  (let [a (get e role) row (get index (get a "name"))]
                                    (need (= a (abi row)) "Callable/raw ABI differs from original row")
                                    (need (= (get e "compiledModule") (get row "sourceModule")) "Entry module provenance differs")
                                    (need (= (get row "ir") (get-in source-rows [(get a "name") "ir"]))
                                          "Actual source-phase callable IR differs")))
                                (let [a (get e "callable") ps (get a "xs")]
                                  (need (and (= 1 (count ps)) (false? (get-in ps [0 "borrow"]))
                                             (#{"object" "tobject" "tagged"} (get-in ps [0 "ty"]))
                                             (#{"object" "tobject" "tagged"} (get a "type"))) "Not an owned boxed bridge"))
                                (need (and (= n (get-in e ["raw" "name"]))
                                           (= "original-interpreter-boxed-lookup" (get e "selection")))
                                      "Unknown original callable selection")
                                (when-let [old (get out n)] (need (= old e) "Conflicting actual entries"))
                                (assoc out n e))))) {} (mapcat #(get % "entries") documents))
        selected (closure index (mapcat #(map (fn [role] (get-in % [role "name"])) ["raw" "callable"]) (vals entries)))]
    (doseq [d documents]
      (need (and (= "lean-native-entry-evidence/1" (get d "schema"))
                 (= "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" (get d "leanCommit"))
                 (= "4.33.1" (get d "leanVersion"))
                 (false? (get d "dynamicClosureProven"))) "Unknown native evidence format/compiler"))
    (need (= (count selected) (count (set (map label (keys selected))))) "Typed Names collide at runtime label")
    {:entries entries :rows selected}))
(defn open! [basis evidence-directory]
  ;; Only these frozen, actually produced bytes can cross the authority boundary.
  (let [documents (mapv #(json/read-str (read-fixed! evidence-directory %)) ["positive.stdout" "imported.stdout"])
        source-rows (reduce merge-exact {} (for [file ["source-export-NativeEntryCases.stdout" "source-export-NativeEntryImported.stdout"]
                                                line (str/split-lines (read-fixed! evidence-directory file))
                                                :let [r (json/read-str line)] :when (= "decl" (get r "kind"))] r))
        {:keys [entries rows]} (metadata! documents source-rows)
        _ (doseq [row (vals rows) :when (get-in row ["ir" "extern"])]
            (.invoke (.getMethod ^Class (:class basis) "validateExternAbi" (into-array Class [java.util.Map])) nil (object-array [row])))
        base (j/prepare-host-program basis [] []) source (j/source-binding base {"native-entry-evidence" pins})
        headers (into {} (for [[n row] rows] [n (j/declaration-header source row (sha (.getBytes (json/write-str row) StandardCharsets/UTF_8)))]))
        registered (j/register-headers base (vec (vals headers)))
        prepared (reduce-kv (fn [c n row] (if (get-in row ["ir" "fdecl"])
                                          (j/materialize-body c (headers n) row (mapv headers (get row "dependencies"))) c)) registered rows)
        ctx (-> prepared (dissoc :task-runtime :profiling-policy) (assoc :explicit true :initializing false))
        holder (atom {:status :opening :thread (Thread/currentThread) :ctx ctx :entries entries :headers headers})
        token (Session.)]
    (locking sessions (.put sessions token holder))
    (try (let [engine (j/machine ctx)] (swap! holder assoc :engine engine :status :idle) token)
         (catch Throwable t (swap! holder assoc :status :failed) (throw (ex-info "Bridge opening failed" {:session token} t))))))
(defn- holder! [session] (locking sessions (or (.get sessions session) (throw (ex-info "Issued bridge Session required" {})))))
(defn owner-packet [session] @(holder! session))
(defn- live! [holder]
  (let [s @holder]
    (need (and (= :idle (:status s)) (identical? (:thread s) (Thread/currentThread))) "Bridge is not live/idle on this thread")
    (let [c (:ctx s) e (:engine s)]
      (need (and (identical? (:class c) (class e)) (identical? (:program c) (field e "program"))
                 (= "idle" (j/phase c e)) (false? (field e "closed")) (false? (field e "disposed"))) "Bridge engine changed")) s))
(defn- nat! [v]
  (need (or (and (= Long (class v)) (not (neg? v)))
            (and (= BigInteger (class v)) (not (neg? (.signum ^BigInteger v))) (<= (.bitLength ^BigInteger v) 4096))) "Exact bounded immutable Nat required") v)
(defn- string! [v]
  (need (and (= String (class v)) (<= (.length ^String v) 65536)
             (= v (String. (.getBytes ^String v StandardCharsets/UTF_8) StandardCharsets/UTF_8))) "Exact bounded Unicode String required") v)
(defn invoke! [session typed-name input]
  (let [holder (holder! session) {:keys [ctx engine entries headers]} (live! holder)
        e (get entries typed-name) signature (get-in e ["typeCheck" "signature"])
        _ (need e "Entry was not actually admitted")
        _ ((if (= signature "nat-to-nat") nat! string!) input)
        n (get-in e ["callable" "name"]) header (headers n)
        slot (object-array [nil :start-pending]) before (j/instructions ctx engine)
        deadline (+ (System/nanoTime) 5000000000)]
    (swap! holder assoc :status :calling :result-slot slot :callable header)
    (try
      (j/start! ctx engine (label n) [input]) (aset slot 1 :running)
      (loop []
        (need (< (System/nanoTime) deadline) "Bridge deadline exhausted; retain failed Session")
        (let [phase (j/phase ctx engine)]
          (case phase
            "running" (let [left (- 20000 (- (j/instructions ctx engine) before))]
                        (need (pos? left) "Bridge instruction budget exhausted")
                        (j/advance! ctx engine (min 128 left)) (recur))
            "complete" nil
            (throw (ex-info "Unexpected pure bridge boundary" {:phase phase})))))
      (need (identical? header (field (field engine "entry") "header")) "Root callable Header changed")
      (aset slot 1 :take-pending)
      (let [v (j/take-result! ctx engine)]
        (aset slot 0 v) (aset slot 1 :owned)
        ((if (= signature "nat-to-nat") nat! string!) v)
        (aset slot 1 :release-pending) (j/release! ctx engine v)
        (aset slot 1 :released) (aset slot 0 nil)
        (need (= "idle" (j/phase ctx engine)) "Result release left active state")
        (swap! holder assoc :status :idle :result-slot nil :callable nil) v)
      (catch Throwable t (swap! holder assoc :status :failed)
        (throw (ex-info "Bridge call failed; preserve Session owner packet, no retry or unwind" {:session session} t))))))
(defn close! [session]
  (let [holder (holder! session) {:keys [ctx engine]} (live! holder)]
    (swap! holder assoc :status :closing)
    (try (j/close! ctx engine) (reset! holder {:status :closed :thread (Thread/currentThread)}) nil
      (catch Throwable t (swap! holder assoc :status :failed) (throw t)))))
