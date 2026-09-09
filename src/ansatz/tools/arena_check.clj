(ns ansatz.tools.arena-check
  "Lean Kernel Arena entry point (https://arena.lean-lang.org/).

   Imports ONE lean4export NDJSON file (format 3.x) into a throwaway in-memory
   environment and kernel-checks every declaration in export order through the
   STRICT admission path — `TypeChecker.checkConstant` for axioms / definitions /
   theorems / opaques / quotient primitives and `checkInductiveBundle` for
   (mutual, nested) inductive groups. The lenient `inferType` is never used.

   Usage:
     clj -M -m ansatz.tools.arena-check [--verbose] [--fuel N] <export.ndjson>
     IN=<export.ndjson> clj -M -m ansatz.tools.arena-check

   Exit codes (the arena convention):
     0  every declaration checks (accept)
     1  the kernel rejects a declaration (reject)
     2  we cannot handle the file (decline): unparseable / unknown record,
        unsupported format version, fuel or stack exhausted
     3  internal checker error (a bug in the checker, never a claim about the proof)

   The decline / reject reason is always written to stderr."
  (:require [ansatz.export.parser :as parser]
            [ansatz.kernel.env :as env]
            [clojure.string :as str])
  (:import [ansatz.kernel ConstantInfo Env ExprStore]
           [java.util ArrayList]))

;; ============================================================
;; Outcomes
;; ============================================================

(def exit-accept 0)
(def exit-reject 1)
(def exit-decline 2)
(def exit-error 3)

(def ^:private default-fuel
  "Fuel per declaration. Lean has no such bound; 20M steps covers every known
  Mathlib declaration. Exhaustion is reported as a DECLINE, never a reject."
  20000000)

(def ^:private stack-size
  "64MB stack: the checker recurses deeply on large proof terms."
  (* 64 1024 1024))

(defn- outcome
  "Build an outcome map. `:exit` is the arena exit code."
  [exit reason & {:as extra}]
  (merge {:exit exit :reason reason} extra))

;; ============================================================
;; Exception classification
;; ============================================================

(defn- root-message [^Throwable t]
  (loop [^Throwable t t, msgs []]
    (let [msgs (conj msgs (or (.getMessage t) (.getName (class t))))]
      (if-let [c (.getCause t)]
        (if (identical? c t) (str/join " <- " msgs) (recur c msgs))
        (str/join " <- " msgs)))))

(defn- resource-limit?
  "Fuel / stack exhaustion: a limit of THIS checker, not a verdict on the proof."
  [^Throwable t]
  (or (instance? StackOverflowError t)
      (instance? OutOfMemoryError t)
      (loop [^Throwable t t]
        (cond
          (nil? t) false
          (some-> (.getMessage t) (str/includes? "fuel exhausted")) true
          (instance? StackOverflowError t) true
          :else (recur (when-not (identical? (.getCause t) t) (.getCause t)))))))

(defn- kernel-rejection?
  "The Java kernel signals a type error as a bare RuntimeException (or ex-info) with a
   message. Anything more specific (NPE, ClassCast, IndexOutOfBounds, IllegalState, …)
   is an internal bug and must surface as a checker ERROR, not a rejection."
  [^Throwable t]
  (and (or (= RuntimeException (class t))
           (instance? clojure.lang.ExceptionInfo t))
       (some? (.getMessage t))))

(defn- classify-throwable [^Throwable t decl-name]
  (cond
    (resource-limit? t)
    (outcome exit-decline (str "resource limit while checking " decl-name ": " (root-message t))
             :decl decl-name :throwable t)

    (kernel-rejection? t)
    (outcome exit-reject (str "kernel rejected " decl-name ": " (root-message t))
             :decl decl-name :throwable t)

    :else
    (outcome exit-error (str "internal checker error on " decl-name ": " (root-message t))
             :decl decl-name :throwable t)))

;; ============================================================
;; Inductive bundle collection (mirrors ansatz.export.replay)
;; ============================================================

(defn- bundle-member? [^objects all-names ^ConstantInfo ci]
  (case (int (.tag ci))
    5 (boolean (some #(= ^Object % (.name ci)) all-names))
    6 (boolean (some #(= ^Object % (.inductName ci)) all-names))
    7 (let [^objects rec-all (.all ci)]
        (boolean
         (and rec-all
              (= (alength all-names) (alength rec-all))
              (every? true? (map = all-names rec-all)))))
    false))

(defn- collect-bundle
  "Split `decls` (whose head is an inductive) into the contiguous bundle it heads
   and the remaining declarations."
  [decls]
  (let [^ConstantInfo head (first decls)
        ^objects all-names (or (.all head) (into-array Object [(.name head)]))]
    (loop [remaining (seq decls) members []]
      (if-let [^ConstantInfo ci (first remaining)]
        (if (bundle-member? all-names ci)
          (recur (next remaining) (conj members ci))
          [members remaining])
        [members nil]))))

(defn- check-bundle ^Env [^Env env members fuel]
  (let [inductives (filterv #(.isInduct ^ConstantInfo %) members)
        ctors (filterv #(.isCtor ^ConstantInfo %) members)
        recursors (filterv #(.isRecursor ^ConstantInfo %) members)
        ^ConstantInfo first-ind (first inductives)
        bundle (env/mk-inductive-bundle (vec (.levelParams first-ind))
                                        (.numParams first-ind)
                                        (.isUnsafe first-ind)
                                        inductives ctors recursors)]
    (env/check-inductive-bundle env bundle fuel)))

;; ============================================================
;; Checking loop
;; ============================================================

(defn- ci-name-str [^ConstantInfo ci] (str (.name ci)))

(defn- check-all
  "Admit every declaration in order through the strict kernel path.
   Returns an outcome map; `:checked` counts admitted declarations."
  [decls fuel verbose?]
  (loop [decls (seq decls)
         env (env/empty-env)
         checked 0]
    (if-let [^ConstantInfo ci (first decls)]
      (cond
        (.isInduct ci)
        (let [[members rest] (collect-bundle decls)
              names (mapv ci-name-str members)
              res (try
                    {:env (check-bundle env members fuel)}
                    (catch Throwable t
                      {:outcome (classify-throwable t (str "inductive bundle " (first names)))}))]
          (if-let [o (:outcome res)]
            (assoc o :checked checked)
            (do (when verbose? (binding [*out* *err*] (println "ok  bundle" (str/join " " names))))
                (recur rest (:env res) (+ checked (count members))))))

        (or (.isCtor ci) (.isRecursor ci))
        ;; A constructor / recursor with no inductive heading its group cannot be
        ;; admitted — the kernel derives and validates these from the inductive.
        (outcome exit-reject
                 (str "kernel rejected " (ci-name-str ci)
                      ": constructor/recursor outside of an inductive declaration")
                 :decl (ci-name-str ci) :checked checked)

        :else
        (let [res (try
                    {:env (env/check-constant env ci fuel)}
                    (catch Throwable t
                      {:outcome (classify-throwable t (ci-name-str ci))}))]
          (if-let [o (:outcome res)]
            (assoc o :checked checked)
            (do (when verbose? (binding [*out* *err*] (println "ok " (name (env/ci-tag ci)) (ci-name-str ci))))
                (recur (next decls) (:env res) (inc checked))))))
      (outcome exit-accept (str "all " checked " declarations check") :checked checked))))

(defn- run-with-large-stack [f]
  (let [result (promise)
        t (Thread. nil
                   (fn [] (deliver result (try (f) (catch Throwable t t))))
                   "ansatz-arena-check"
                   (long stack-size))]
    (.start t)
    (.join t)
    (let [r @result]
      (if (instance? Throwable r) (throw r) r))))

;; ============================================================
;; Parsing
;; ============================================================

(def ^:private supported-format-major "3")

(defn- format-version [meta]
  (get-in meta ["format" "version"]))

(defn parse-export
  "Parse the export. Returns {:decls [...] :meta ...} or an outcome map with :exit."
  [path]
  (let [st (try (parser/parse-ndjson-file path)
                (catch Throwable t
                  (outcome exit-decline (str "cannot parse export: " (root-message t)) :throwable t)))]
    (if (:exit st)
      st
      (do
        (.close ^ExprStore (:exprs st))
        (let [ver (format-version (:meta st))]
          (cond
            (nil? ver)
            (outcome exit-decline "export has no leading meta record with a format version (expected lean4export format 3.x)")

            (not (str/starts-with? (str ver) (str supported-format-major ".")))
            (outcome exit-decline (str "unsupported export format version " ver " (we read 3.x)"))

            :else
            {:decls (:decls st)
             :meta (:meta st)
             :num-names (.size ^ArrayList (:names st))}))))))

;; ============================================================
;; CLI
;; ============================================================

(defn check-file
  "Check one export file. Returns the outcome map (never throws, never exits)."
  [path & {:keys [fuel verbose?] :or {fuel default-fuel verbose? false}}]
  (try
    ;; Parse on the large-stack thread too: resolving a deeply nested export
    ;; (the arena's `perf/*-ladder` files) recurses as deep as the term.
    (let [parsed (run-with-large-stack #(parse-export path))]
      (if (:exit parsed)
        parsed
        (let [start (System/currentTimeMillis)
              o (run-with-large-stack #(check-all (:decls parsed) fuel verbose?))]
          (assoc o
                 :decls (count (:decls parsed))
                 :lean-version (get-in parsed [:meta "lean" "version"])
                 :elapsed-ms (- (System/currentTimeMillis) start)))))
    (catch Throwable t
      (outcome exit-error (str "internal checker error: " (root-message t)) :throwable t))))

(defn- usage []
  (binding [*out* *err*]
    (println "Usage: clj -M -m ansatz.tools.arena-check [--verbose] [--fuel N] <export.ndjson>")
    (println "       IN=<export.ndjson> clj -M -m ansatz.tools.arena-check")))

(defn- parse-args [args]
  (loop [args (seq args) opts {}]
    (if-let [a (first args)]
      (case a
        "--verbose" (recur (next args) (assoc opts :verbose? true))
        "--fuel" (recur (nnext args) (assoc opts :fuel (Long/parseLong (second args))))
        (recur (next args) (assoc opts :path a)))
      opts)))

(defn -main [& args]
  (let [{:keys [path fuel verbose?]} (parse-args args)
        path (or path (System/getenv "IN"))]
    (when (str/blank? path)
      (usage)
      (System/exit exit-decline))
    (let [{:keys [exit reason throwable checked decls elapsed-ms lean-version]}
          (check-file path :fuel (or fuel default-fuel) :verbose? verbose?)
          label (case (long exit) 0 "ACCEPT" 1 "REJECT" 2 "DECLINE" "ERROR")]
      (binding [*out* *err*]
        (println (str "arena-check " label ": " reason))
        (when (and throwable (= exit exit-error))
          (.printStackTrace ^Throwable throwable (java.io.PrintWriter. *out* true)))
        (when decls
          (println (str "  " (or checked 0) "/" decls " declarations admitted"
                        (when lean-version (str ", lean " lean-version))
                        (when elapsed-ms (str ", " elapsed-ms " ms")))))
        (flush))
      (flush)
      (shutdown-agents)
      (System/exit exit))))
