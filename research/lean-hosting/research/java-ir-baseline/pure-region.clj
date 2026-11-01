(ns java-ir-pure-region
  "Private research adapter: acyclic no-extern raw IR, Nat/String boundaries.
   This is neither frontend admission nor a general replacement for World execution."
  (:require [clojure.walk :as walk]
            [java-ir-baseline :as j]
            [prototype.import-ir :as ir]
            [prototype.interop-codec :as codec]
            [prototype.machine :as m]))

(defn- check! [condition message data]
  (when-not condition (throw (ex-info message data))))

(defn- expression-targets [expr]
  (check! (and (map? expr) (= 1 (count expr))) "Invalid pure expression" {})
  (let [[op data] (first expr)]
    (case op
      "fap" #{(get data "c")}
      "lit" (let [lit (get data "v")]
                (check! (and (map? lit) (= 1 (count lit))
                             (or (and (contains? lit "num")
                                      (integer? (get-in lit ["num" "v"]))
                                      (<= 0 (get-in lit ["num" "v"])))
                                 (and (contains? lit "str")
                                      (string? (get-in lit ["str" "v"])))))
                        "Pure literals must be Nat or String" {})
                (when (contains? lit "str")
                  (codec/encode nil :string (get-in lit ["str" "v"])))
                #{})
      ;; Sharing tests observe representation/constant-cache ownership, which
      ;; differs across this codec boundary even for otherwise pure code.
      ("ctor" "proj") #{}
      (throw (ex-info "Instruction outside pure region vocabulary" {:expression op})))))

(defn- body-targets [[op & args :as body]]
  (check! (vector? body) "Pure body must be immutable vector" {})
  (case op
    "vdecl" (into (expression-targets (nth args 2)) (body-targets (nth args 3)))
    ("inc" "dec") (body-targets (last args))
    "case" (reduce into #{} (map #(body-targets (last %)) (nth args 3)))
    ("ret" "unreachable") #{}
    (throw (ex-info "Instruction outside pure region vocabulary" {:instruction op}))))

(defn- closure-rows [rows target]
  (check! (and (vector? rows) (every? map? rows)) "Original rows must be immutable vector" {})
  (let [decls (filter #(= "decl" (get % "kind")) rows)
        groups (group-by #(get % "name") decls)]
    (check! (every? #(= 1 (count %)) (vals groups)) "Duplicate pure declaration" {})
    (letfn [(visit [name visiting done]
              (check! (not (contains? visiting name)) "Recursive pure regions are unsupported" {:name name})
              (if (contains? done name) done
                (let [row (first (get groups name)) f (get-in row ["ir" "fdecl"])]
                  (check! (and row f (= name (get f "f"))) "Pure region requires original fdecl" {:name name})
                  (check! (contains? #{nil "ordinary"} (get-in row ["runtime" "role"]))
                          "Pure region excludes initialized/global declarations" {:name name})
                  (check! (every? #(contains? #{"object" "tobject" "tagged"} (get % "ty")) (get f "xs"))
                          "Pure region requires boxed parameters" {:name name})
                  (check! (contains? #{"object" "tobject" "tagged"} (get f "type"))
                          "Pure region requires boxed results" {:name name})
                  (let [deps (body-targets (get f "body"))
                        done (reduce #(visit %2 (conj visiting name) %1) done deps)]
                    (assoc done name row)))))]
      (let [selected (visit target #{} {})]
        (filterv #(contains? selected (get % "name")) decls)))))

(defn- owners! [world args params]
  (doseq [[value occurrences] (group-by first (map vector args params))
          :when (m/ref? value)]
    (let [node (m/node world value)
          owned (count (remove #(get-in % [1 :borrow]) occurrences))
          borrowed? (some #(get-in % [1 :borrow]) occurrences)]
      ;; A scalar leaf makes each individual immutable release atomic. Imported
      ;; RC0 leaves remain borrowed from their explicit host source lease.
      (check! (and (contains? #{:string :mpz} (:kind node)) (empty? (:fields node))
                   (integer? (:rc node)) (<= 0 (:rc node))
                   (or (zero? (:rc node))
                       (if borrowed? (< owned (:rc node)) (<= owned (:rc node)))))
              "Insufficient or unsupported legacy argument owners" {:value value :owned owned}))))

(defn- java-argument [descriptor value]
  (if (= descriptor :nat)
    (let [n (biginteger value)]
      (if (<= (.bitLength n) 63) (Long/valueOf (.longValue n)) n))
    value))

(defn prepare
  "Return a private callable [world encoded-args] -> canonical completed World.
   BASIS is the reflection class-basis; ROWS are original immutable raw captures.
   SPEC has :functions (exact legacy identity), :target (structured Lean name),
   :params [{:codec :nat/:string :borrow Boolean}], and :result :nat/:string.
   Reprepares the exact selected rows; checks their legacy lowering structurally.
   No externs, dynamic calls, globals, loops, scalar lanes or recursion accepted.
   Each invocation creates and closes a fresh engine; no Java value escapes.
   Decode borrows. Legacy argument owners transfer only after successful Java
   execution and result encoding. Failures carry the latest actual World and
   remaining occurrence indices; callers must never fall back after entry."
  [basis rows {:keys [functions target params result] :as spec}]
  (check! (= #{:functions :target :params :result} (set (keys spec))) "Invalid pure region specification" {})
  (check! (and (map? functions) (vector? params) (contains? #{:nat :string} result)
               (every? #(and (= #{:codec :borrow} (set (keys %)))
                             (contains? #{:nat :string} (:codec %))
                             (instance? Boolean (:borrow %))) params))
          "Pure region requires explicit Nat/String codecs and ownership" {})
  (let [selected (closure-rows rows target)
        root (first (filter #(= target (get % "name")) selected))
        root-params (get-in root ["ir" "fdecl" "xs"])]
    (check! (= (mapv :borrow params) (mapv #(get % "borrow") root-params))
            "Pure region parameter ABI mismatch" {})
    (check! (and (every? true? (map #(or (= :nat (:codec %1))
                                         (contains? #{"object" "tobject"} (get %2 "ty")))
                                   params root-params))
                 (or (= result :nat)
                     (contains? #{"object" "tobject"} (get-in root ["ir" "fdecl" "type"]))))
            "String codec requires an object ABI" {})
    (doseq [row selected]
      (let [[name lowered] (ir/lower-declaration (walk/keywordize-keys row)) actual (get functions name)]
        (check! (and (= lowered actual)
                     (= (:runtime-param-types (meta lowered)) (:runtime-param-types (meta actual))))
                "Legacy executable differs from original row lowering" {:name name})))
    (let [ctx (assoc basis :program (j/invoke-static (:prepare basis) [selected]) :explicit false)
          label (ir/name-label target)]
      ;; Resolve before a World can be supplied, independently of metadata.
      (j/function-id ctx label)
      (fn [world args]
        (let [checkpoint (volatile! world) stage (volatile! :preflight)
              entered? (volatile! false)
              remaining (volatile! (vec (keep-indexed #(when-not (:borrow %2) %1) params)))
              encoded-result (volatile! nil)]
          (try
            (check! (and (vector? args) (= (count args) (count params))) "Pure region arity mismatch" {})
            (check! (identical? functions (:functions world)) "Pure region executable identity changed" {})
            ;; Validate canonical completion controls before any entry/transfer.
            (m/complete-closed-call world world functions target 0)
            (owners! world args params)
            (let [decoded (mapv #(codec/decode-boxed world (:codec %1) %2) params args)
                  java-args (mapv #(java-argument (:codec %1) %2) params decoded)
                  engine (j/machine ctx)
                  answer (try
                           (vreset! stage :execute) (vreset! entered? true)
                           (let [value (j/call ctx engine label java-args)]
                             (try
                               (check! (or (string? value) (instance? Long value) (instance? java.math.BigInteger value))
                                       "Java result outside Nat/String boundary" {})
                               value
                               (finally (j/release! ctx engine value))))
                           (finally (j/close! ctx engine)))]
              (vreset! stage :encode)
              (let [[next-world value] (codec/encode-boxed @checkpoint result answer)]
                (vreset! checkpoint next-world) (vreset! encoded-result value)
                (vreset! stage :release)
                (doseq [index @remaining]
                  (vreset! checkpoint (m/release @checkpoint (nth args index) 1))
                  (vswap! remaining #(vec (rest %))))
                (vreset! stage :complete)
                (m/complete-closed-call world @checkpoint functions target value)))
            (catch Throwable cause
              (throw (ex-info "Pure Java region failed; no fallback is authorized"
                              {:checkpoint @checkpoint :stage @stage :entered? @entered?
                               :region-arguments args
                               :remaining-argument-indices @remaining
                               :encoded-result @encoded-result}
                              cause)))))))))
