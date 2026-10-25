(ns prototype.runtime-abi
  "Raw guest runtime primitives, distinct from public typed host interop."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [prototype.machine :as m]
            [prototype.import-ir :as ir]
            [prototype.runtime-prim :as prim]
            [prototype.runtime-thunk :as thunk]
            [prototype.runtime-task :as task]
            [prototype.runtime-mvars :as mvars]
            [prototype.runtime-expr-mvars :as expr-mvars]
            [prototype.runtime-expr-search :as search]
            [prototype.runtime-expr-replace :as expr-replace]))

(defn symbol-for [ext]
  ;; Match Lean.getExternEntryFor: first entry for `all` or the C ABI backend.
  ;; An unsupported inline entry takes precedence over later standard entries.
  (let [entry (first (filter (fn [entry]
                               (let [data (val (first entry))]
                                 (contains? #{["str" ["anonymous"] "all"] ["str" ["anonymous"] "c"]}
                                            (:backend data)))) (get-in ext [:ext :entries])))]
    (get-in entry [:standard :fn])))

(def signatures
  (delay (edn/read-string (slurp (io/resource "prototype/runtime_signatures.edn")))))

(defn supported? [ext] (contains? prim/supported-symbols (symbol-for ext)))

(defn- name! [name]
  (loop [part name]
    (when-not (vector? part) (m/fail "Invalid export target name" {:name name}))
    (case (first part)
      "anonymous" (when-not (= 1 (count part)) (m/fail "Invalid export target name" {:name name}))
      "str" (do (when-not (and (= 3 (count part)) (string? (nth part 2)))
                  (m/fail "Invalid export target name" {:name name}))
                (recur (second part)))
      "num" (do (when-not (and (= 3 (count part))
                               (or (and (integer? (nth part 2)) (not (neg? (nth part 2))))
                                   (and (string? (nth part 2)) (re-matches #"0|[1-9][0-9]*" (nth part 2)))))
                  (m/fail "Invalid export target name" {:name name}))
                (recur (second part)))
      (m/fail "Invalid export target name" {:name name}))) name)

(defn- export-targets [manifests]
  (reduce
   (fn [targets {:keys [symbol name sourceModule]}]
     (when-not (and (string? symbol) (seq symbol)) (m/fail "Invalid exported symbol" {:symbol symbol}))
     (name! name)
     (when sourceModule (name! sourceModule))
     (when-let [old (get targets symbol)]
       (when-not (= old name) (m/fail "Conflicting export targets" {:symbol symbol :targets #{old name}})))
     (assoc targets symbol name)) {} (mapcat :exports manifests)))

(defn with-export-aliases
  "Overlay a metadata-only alias catalogue (e.g. index-bundles of ExportAliases).
  Validates the pinned producer and symbol inventory without reading any body.
  Target existence/body/ownership/type checks remain lazy, when an extern is used.
  Declaration indexes, reader and storage ownership are preserved unchanged."
  [catalogue aliases]
  (when (seq (:declarations aliases)) (m/fail "Export alias overlay must contain metadata only" {}))
  (when-not (seq (:manifests aliases)) (m/fail "Export alias overlay has no manifests" {}))
  (doseq [manifest (:manifests aliases)]
    (ir/validate-manifest! manifest)
    (when-not (= (get prim/pinned-build "lean_get_githash") (:leanCommit manifest))
      (m/fail "Export alias producer commit mismatch" {:commit (:leanCommit manifest)}))
    (when-not (and (= "manifest" (:kind manifest)) (map? (:runtimeProfile manifest)) (vector? (:exports manifest))
                   (nil? (:initializationPlan manifest)))
      (m/fail "Invalid metadata-only export alias manifest" {:manifest manifest})))
  (let [manifests (into (vec (:manifests catalogue)) (:manifests aliases))
        targets (export-targets manifests)]
    (assoc catalogue :manifests manifests ::export-manifests manifests ::export-targets targets)))

(defn with-consumer-redirects
  "Explicit host configuration, separate from producer exports/CAS evidence.
   Each symbol maps to {:original-row <authenticated producer row> :target Name}.
   Installation does not authenticate supplied bytes or confer kernel authority;
   the enclosing preparation profile must do that. Every later lowering checks
   the actual source row and actual target ABI. Existing redirects cannot change."
  [catalogue redirects]
  (when-not (map? redirects) (m/fail "Invalid consumer redirect configuration" {}))
  (doseq [[symbol {:keys [original-row target] :as redirect}] redirects]
    (when-not (and (= #{:original-row :target} (set (keys redirect)))
                   (string? symbol) (seq symbol) (= "decl" (:kind original-row))
                   (= (:name original-row) (get-in original-row [:ir :extern :f]))
                   (= symbol (some-> original-row :ir :extern symbol-for))
                   (nil? (:redirect original-row)))
      (m/fail "Invalid consumer redirect origin" {:symbol symbol}))
    (name! target)
    (when-let [old (get (::consumer-redirects catalogue) symbol)]
      (when-not (= old redirect) (m/fail "Conflicting consumer redirect" {:symbol symbol}))))
  (update catalogue ::consumer-redirects merge redirects))

(defn- resolve-export-redirect [catalogue row]
  (if-let [ext (get-in row [:ir :extern])]
    (let [symbol (symbol-for ext)
          targets (if (identical? (::export-manifests catalogue) (:manifests catalogue))
                    (or (::export-targets catalogue) (export-targets (:manifests catalogue)))
                    (export-targets (:manifests catalogue)))
          consumer (get (::consumer-redirects catalogue) symbol)
          _ (when consumer
              (when-not (= (:name row) (get-in consumer [:original-row :name]))
                (m/fail "Consumer redirect source name mismatch" {:symbol symbol}))
              ;; Reuse ordinary reconciliation: same IR/dependency edges and
              ;; redirect metadata, with only its existing source-local rules.
              (ir/reconcile-declarations (:original-row consumer) row))
          manifest-target (get targets symbol)
          explicit-target (get-in row [:redirect :name])
          selected (remove nil? [(:target consumer) explicit-target manifest-target])
          target (first selected)]
      (when (> (count (set selected)) 1)
        (m/fail "Conflicting explicit export redirect" {:symbol symbol :targets selected}))
      (if target
        (let [target-row (if-let [read-declaration (:read-declaration catalogue)]
                           (read-declaration target) (get-in catalogue [:declarations target]))
              f (get-in target-row [:ir :fdecl])]
          (when-not f (m/fail "Export target has no guest function body" {:symbol symbol :target target}))
          (when-not (= target (:name target-row) (:f f))
            (m/fail "Export target name mismatch" {:target target :row-name (:name target-row) :function (:f f)}))
          (when-let [declared (:redirect row)]
            (let [shape (fn [params type] {:params (mapv #(select-keys % [:ty :borrow]) params) :return-type type})]
              (when-not (= (shape (:params declared) (:type declared)) (shape (:xs f) (:type f)))
                (m/fail "Export redirect signature mismatch" {:name (:name row) :target target :stored-signature true}))))
          ;; Check against the actual selected body, never merely a producer's
          ;; stored copy of a signature. lower-redirect enforces the ABI below.
          (assoc row :redirect {:name target :params (:xs f) :type (:type f)}))
        row)) row))

(defn- lower-redirect [row]
  (let [ext (get-in row [:ir :extern]) redirect (:redirect row)
        shape (fn [params type] {:params (mapv #(select-keys % [:ty :borrow]) params) :return-type type})
        params (mapv #(get-in % [:x :idx]) (:xs ext))]
    (when-not (and ext (= (shape (:xs ext) (:type ext)) (shape (:params redirect) (:type redirect))))
      (m/fail "Export redirect signature mismatch" {:name (:name row) :redirect redirect}))
    [(:f ext) {:params params :export-redirect (:name redirect)
              :body [:tail [:direct (:name redirect)] (mapv #(vector :var %) params)]}]))

(def profiler-option-getter
  ;; Pinned 4.33.1 Lean/Util/Profile.lean's exported lean_get_profiler body.
  ;; It owns its Options argument. Its actual guest implementation performs the
  ;; Options/NameMap lookup and applies the registered false default.
  (reduce (fn [parent part] (if (number? part) ["num" parent (str part)] ["str" parent part]))
          ["anonymous"] ["_private" "Lean" "Util" "Profile" 0 "Lean" "get_profiler"]))

(defn profileit-body [params dest]
  (let [[_ category options function declaration] params]
    [:inc [:var options] 1
     [:call dest [:direct profiler-option-getter] [[:var options]]
      [:case [:var dest]
       [[0 [:dec [:var declaration] 1 [:tail [:closure [:var function]] [[:imm 0]]]]]
        [1 [:trap {:name ["str" ["str" ["anonymous"] "Lean"] "profileit"]
                   :symbol "lean_profileit" :runtime-limit :enabled-profiling
                   :message "Enabled profiling requires injected clock/event capabilities"}
             [[:var category] [:var options]]]]]]]]))

(defn lower [row]
  (if (:redirect row) (lower-redirect row)
  (if-let [ext (get-in row [:ir :extern])]
    (let [symbol (symbol-for ext) spec (get prim/supported-symbols symbol)
          params (mapv #(get-in % [:x :idx]) (:xs ext))
          arities (or (:arities spec) #{(:arity spec)})
          dest (inc (reduce max 0 params))]
      (when-not (and spec (contains? arities (count params)))
        (m/fail "Unsupported raw runtime primitive signature" {:symbol symbol :params (:xs ext)}))
      (let [shape {:params (mapv #(select-keys % [:ty :borrow]) (:xs ext)) :return-type (:type ext)}]
        (when-not (some #{shape} (get @signatures symbol))
          (m/fail "Unrecognized raw runtime ownership/type signature" {:symbol symbol :shape shape})))
      (doseq [ty (cons (:type ext) (map :ty (:xs ext)))] (ir/type! ty))
      [(:f ext) (cond-> {:params params :runtime-extern symbol
                :body (cond
                        (= symbol "lean_replace_expr") (expr-replace/body params dest)
                        (= symbol "lean_find_ext_expr") (search/ext-body params dest)
                        (= symbol "lean_find_expr") (search/body params dest)
                        (= symbol "lean_instantiate_expr_mvars") (expr-mvars/body params dest)
                        (= symbol "lean_instantiate_level_mvars") (mvars/body params dest)
                        (= symbol "lean_profileit") (profileit-body params dest)
                        (= symbol "lean_thunk_get_own") (thunk/get-own-body (second params) dest)
                        (= symbol "lean_task_get_own") (task/get-body (second params) dest)
                        (= symbol "lean_io_wait_any") (task/wait-any-body (second params) dest)
                        (= symbol "lean_io_wait") [:tail [:direct task/get-target] [[:var (first params)] [:var (second params)]]]
                        (contains? #{"lean_task_spawn" "lean_task_map" "lean_task_bind" "lean_io_as_task" "lean_io_map_task" "lean_io_bind_task"} symbol)
                        (task/registration-body symbol params dest)
                        (= symbol "lean_io_promise_resolve")
                        [:let dest [:runtime symbol (mapv #(vector :var %) params)] (task/drain-body (inc dest) true)]
                        :else [:let dest [:runtime symbol (mapv #(vector :var %) params)] [:return [:var dest]]])}
                 (contains? task/supported-symbols symbol) (assoc :runtime-dependencies [task/get-target])
                 (contains? expr-mvars/supported-symbols symbol) (assoc :runtime-dependencies expr-mvars/dependencies)
                 (contains? mvars/supported-symbols symbol) (assoc :runtime-dependencies [mvars/getter mvars/setter]))])
    (ir/lower-declaration row))))

(defn lower-deferred
  "Admit unsupported externs only as named fail-on-execution traps. This is an
  explicit reachability experiment, never a replacement implementation."
  [row]
  (if-let [ext (get-in row [:ir :extern])]
    (if (or (:redirect row) (supported? ext)) (lower row)
      [(:f ext) {:params (mapv #(get-in % [:x :idx]) (:xs ext))
                :deferred-extern {:name (:name row) :symbol (symbol-for ext) :signature (select-keys ext [:xs :type])}
                :body [:trap {:name (:name row) :symbol (symbol-for ext)}
                       (mapv #(vector :var (get-in % [:x :idx])) (:xs ext))]}])
    (ir/lower-declaration row)))

(defn lower-catalogue
  "Strict lowering with verified guest export aliases. Missing bodies and ABI
  mismatches are hard errors, as are unsupported non-aliased runtime primitives."
  [catalogue row]
  (lower (resolve-export-redirect catalogue row)))

(defn lower-deferred-catalogue
  "Demand-execution admission: unsupported function lowering becomes a named
  trap. Conflicting ABI signatures and missing declarations remain hard errors."
  [catalogue row]
  (try
    (lower-deferred (resolve-export-redirect catalogue row))
    (catch clojure.lang.ExceptionInfo cause
      (if (and (get-in row [:ir :fdecl])
               (contains? #{"Unsupported imported runtime type" "Unsupported imported expression" "Unsupported imported instruction" "Unsupported scalar storage type"}
                          (.getMessage cause)))
        (let [f (get-in row [:ir :fdecl]) params (mapv #(get-in % [:x :idx]) (:xs f))
              reason {:message (.getMessage cause) :data (ex-data cause)}]
          [(:f f) {:params params :deferred-declaration reason
                    :body [:trap {:name (:name row) :lowering-error reason} (mapv #(vector :var %) params)]}])
        (throw cause)))))
