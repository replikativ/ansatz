(ns prototype.program-install
  "Immutable, top-level admission of pinned RuntimeCompileShim IR. Installation
  does not execute initialization or replace existing callback targets."
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.import-ir :as ir]
            [prototype.initialization :as initialization]
            [prototype.machine :as m]
            [prototype.runtime-abi :as abi]
            [prototype.runtime-prim :as prim]
            [prototype.walk :as walk]))

(defn- name! [n]
  (loop [p n]
    (when-not (vector? p) (m/fail "Invalid compiled declaration name" {:name n}))
    (case (first p)
      "anonymous" (when-not (= 1 (count p)) (m/fail "Invalid compiled declaration name" {:name n}))
      "str" (do (when-not (and (= 3 (count p)) (string? (nth p 2)))
                  (m/fail "Invalid compiled declaration name" {:name n})) (recur (second p)))
      "num" (do (when-not (and (= 3 (count p))
                               (or (and (integer? (nth p 2)) (not (neg? (nth p 2))))
                                   (and (string? (nth p 2)) (re-matches #"0|[1-9][0-9]*" (nth p 2)))))
                  (m/fail "Invalid compiled declaration name" {:name n})) (recur (second p)))
      (m/fail "Invalid compiled declaration name" {:name n}))) n)

(defn- natural! [n label]
  (when-not (and (integer? n) (<= 0 n Integer/MAX_VALUE))
    (m/fail "Invalid compiled register or index" {:field label :value n})) n)

(defn- parameters! [params]
  (when-not (vector? params) (m/fail "Invalid compiled parameters" {}))
  (doseq [{:keys [x ty borrow]} params]
    (natural! (:idx x) :parameter)
    (ir/type! ty)
    (when-not (boolean? borrow) (m/fail "Missing compiled ownership annotation" {:parameter x})))
  (when-not (= (count params) (count (set (map #(get-in % [:x :idx]) params))))
    (m/fail "Duplicate compiled parameter" {})))

(defn- signature [decl]
  {:params (mapv #(select-keys % [:ty :borrow]) (:xs decl)) :return-type (:type decl)})

(defn- declaration! [row]
  (let [decl (or (get-in row [:ir :fdecl]) (get-in row [:ir :extern]))]
    (when-not (and (= "decl" (:kind row)) decl
                   (= 1 (count (:ir row))))
      (m/fail "Missing compiled declaration body" {:name (:name row)}))
    (name! (:name row))
    (when-not (= (:name row) (:f decl))
      (m/fail "Compiled declaration name mismatch" {:name (:name row) :actual (:f decl)}))
    (parameters! (:xs decl)) (ir/type! (:type decl))
    (when-let [role (get-in row [:runtime :role])]
      (when-not (contains? #{"ordinary" "closed" "ground" "value" "initialized"} role)
        (m/fail "Invalid compiled global role" {:name (:name row) :role role})))
    (when (= "initialized" (get-in row [:runtime :role]))
      (name! (get-in row [:runtime :initializer])))
    ;; Validate every raw node before lowering, including nodes subsequently
    ;; optimized away by tail-call recognition. No recursive tree-seq/hash.
    (doseq [node (walk/forms (:body decl))]
      (when (map? node)
        (when (contains? node :idx) (natural! (:idx node) :register))
        (when (contains? node :cidx)
          (when-not (and (integer? (:cidx node)) (<= 0 (:cidx node) 243))
            (m/fail "Invalid compiled constructor tag" {:constructor node})))
        (when-let [ctor (:ctor node)]
          (ir/layout! (:i ctor))
          (when-not (and (integer? (get-in ctor [:i :cidx])) (<= 0 (get-in ctor [:i :cidx]) 243))
            (m/fail "Invalid compiled constructor tag" {:constructor (:i ctor)})))
        (when-let [ap (:ap node)]
          (when-not (seq (:ys ap)) (m/fail "Empty compiled boxed application" {:name (:name row)}))))
      (when (vector? node)
        (case (first node)
          "jdecl" (parameters! (nth node 2))
          "vdecl" (ir/type! (nth node 2))
          "case" (ir/type! (nth node 3))
          nil)))
    decl))

(defn- strict-manifest! [manifest]
  (ir/validate-manifest! manifest)
  (when-not (and (= "manifest" (:kind manifest))
                 (= "RuntimeCompileShim.exportCompiled" (:producer manifest))
                 (= (get prim/pinned-build "lean_get_githash") (:leanCommit manifest))
                 (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest))
                 (= "all-local-declarations" (:initializationPlanScope manifest)))
    (m/fail "Untrusted compiled IR producer/profile" {:producer (:producer manifest) :commit (:leanCommit manifest)}))
  (when-not (and (vector? (:requestedRoots manifest)) (seq (:requestedRoots manifest))
                 (vector? (:entryPoints manifest)) (vector? (:missingDependencies manifest)))
    (m/fail "Incomplete compiled IR manifest" {}))
  (doseq [n (concat (:requestedRoots manifest) (:missingDependencies manifest))] (name! n))
  manifest)

(defn bundle-catalogue
  "Decode a complete source-local JSONL bundle, or accept a raw/indexed catalogue.
  An indexed catalogue must expose :read-declaration; its index is not decoded."
  [bundle]
  (if (string? bundle)
    (let [rows (mapv #(json/read-str % :key-fn keyword :bigdec false)
                     (remove str/blank? (str/split-lines bundle)))
          declarations (rest rows)]
      (when-not (= (count declarations) (count (set (map :name declarations))))
        (m/fail "Duplicate compiled declaration" {}))
      {:manifests [(first rows)] :declarations (into {} (map (juxt :name identity)) declarations)})
    (if (and (map? bundle) (map? (:declarations bundle))) bundle
      (m/fail "Expected compiled JSONL or catalogue" {}))))

(defn- read-row [catalogue n]
  (if-let [read-declaration (:read-declaration catalogue)]
    (read-declaration n) (get-in catalogue [:declarations n])))

(defn- body-dependencies [body]
  (into #{} (keep (fn [node]
                   (when (vector? node)
                     (case (first node)
                       :closure (when (= 3 (count node)) (name! (second node)))
                       :direct (name! (second node))
                       (:global :begin-init) (name! (nth node 2))
                       nil)))) (walk/forms body)))

(defn- with-signature [f decl]
  (with-meta f (assoc (meta f) :runtime-param-types (mapv :ty (:xs decl))
                     :runtime-signature (signature decl))))

(defn- validate-calls! [new-functions functions]
  (doseq [[name f] new-functions node (walk/forms (:body f))
          :when (vector? node)]
    (let [[op a b c] node
          [target args partial?] (case op
                                   :closure (when (= 3 (count node)) [a b true])
                                   :call (when (= :direct (first b)) [(second b) c false])
                                   :tail (when (= :direct (first a)) [(second a) b false])
                                   nil)]
      (when target
        (let [callee (get functions target) arity (count (:params callee))]
          (when-not callee (m/fail "Missing compiled call target" {:name name :target target}))
          (when-not (if partial? (< (count args) arity) (= (count args) arity))
            (m/fail "Compiled call arity mismatch" {:name name :target target :arity arity :arguments (count args) :partial partial?})))))))

(defn- initializer-arguments [functions name]
  (let [f (get functions name)]
    (when-not (and f (contains? #{[] ["void"] ["erased"]} (:runtime-param-types (meta f)))
                  (<= (count (:params f)) 1))
      (m/fail "Compiled initializer must accept only an erased world" {:name name}))
    (mapv (constantly [:imm m/erased]) (:params f))))

(defn- wrap-new-globals [old-functions new-functions globals reserved]
  (let [initial (merge old-functions new-functions)
        add! (fn [functions n f]
               (when (or (contains? initial n) (contains? functions n) (contains? globals n) (contains? reserved n))
                 (m/fail "Compiled synthetic global name collision" {:name n}))
               (assoc functions n f))]
    (reduce-kv
     (fn [functions name f]
       (if (or (:global-role f) (:runtime-initializer f))
         (let [target ["str" name "_ansatz_global_initializer"]]
           (when (or (seq (:params f)) (contains? globals name))
             (m/fail "Compiled global conflicts with existing state or has parameters" {:name name}))
           (if-let [initializer (:runtime-initializer f)]
             (-> (add! functions target {:params [] :body [:begin-init name initializer
                                                         (initializer-arguments initial initializer) (:result-type f)]})
                 (assoc name (assoc f :init-target target)))
             (-> (add! functions target (dissoc f :global-role))
                 (assoc name (with-meta (assoc f :body [:global name target]) (meta f))))))
         (assoc functions name f))) old-functions new-functions)))

(defn install
  "Install NEW compiled IR in an immutable idle world. Options:
  :catalogue lazy backing catalogue for dependencies/export signatures;
  :protected-names additional reserved structured Names;
  :existing-signatures trusted ABI shapes for old export targets lacking metadata;
  :completed-local-actions set of producer action maps already executed;
  :lower-extern trusted extern-only lowerer (row -> [name function], or nil to
    use the normal catalogue-aware ABI lowerer). It must validate host ABI;
  :research-traps? explicitly admit unknown externs as named execution traps.
  Returns :world, :boxed-entrypoints, and ordered :pending-local-initializers.
  Pending actions contain :call-target and :completion-key. No guest code runs;
  caller must execute and record completed IO actions explicitly."
  ([world bundle] (install world bundle {}))
  ([world bundle {:keys [catalogue protected-names completed-local-actions research-traps? existing-signatures lower-extern]
                 :or {completed-local-actions #{}}}]
   (when (and lower-extern (not (fn? lower-extern)))
     (m/fail "Compiled extern lowerer must be a trusted function" {}))
   (when (contains? #{:running :paused :suspended :host-call} (:status world))
     (m/fail "Compiled installation requires an idle top-level world" {:status (:status world)}))
   (let [candidate (bundle-catalogue bundle)
         _ (when-not (= 1 (count (:manifests candidate))) (m/fail "Expected one compiled IR manifest" {}))
         manifest (strict-manifest! (first (:manifests candidate)))
         _ (when-not (set? completed-local-actions) (m/fail "Completed local actions must be a set" {}))
         plan (:initializationPlan manifest)
         action-roots (initialization/action-names plan)
         _ (when-not (and (vector? (:actions plan)) (boolean? (:moduleSystem plan)))
             (m/fail "Incomplete compiled initialization plan" {}))
         _ (doseq [{:keys [action meta]} (:actions plan)]
             (when-not (boolean? meta) (m/fail "Missing compiled initializer phase annotation" {}))
             (name! (:name action)) (name! (:target action))
             (when (and (= "value" (:kind action)) (not= (:name action) (:target action)))
               (m/fail "Compiled value initializer target mismatch" {:action action})))
         _ (when (:moduleSystem plan) (m/fail "Compiled module-system local phases require explicit planning" {}))
         old (:functions world)
         _ (when-not (map? old) (m/fail "Missing existing immutable program" {}))
         protected (into (set (keys old)) protected-names)
         backing-valid (delay
                         (when-not (seq (:manifests catalogue))
                           (m/fail "Dependency catalogue lacks producer/profile" {}))
                         (doseq [manifest (:manifests catalogue)]
                           (ir/validate-manifest! manifest)
                           (when-not (and (= (get prim/pinned-build "lean_get_githash") (:leanCommit manifest))
                                          (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile manifest)))
                             (m/fail "Dependency producer/profile mismatch" {:commit (:leanCommit manifest)}))))
         read-backing (fn [n]
                        (when catalogue
                          (when-let [row (read-row catalogue n)]
                            (force backing-valid) row)))
         reader (fn [n]
                  (let [row (read-row candidate n)]
                    (if (= "decl" (:kind row)) row
                      (or (read-backing n) row))))
         ;; Alias validation must read authoritative old signatures, rather than
         ;; trusting candidate-imported copies of protected declarations.
         alias-reader (fn [n]
                        (if (contains? old n)
                          (let [base-row (read-backing n)
                                fdecl (get-in base-row [:ir :fdecl])
                                shape (or (when fdecl (signature (declaration! base-row)))
                                          (get existing-signatures n)
                                          (:runtime-signature (meta (get old n))))]
                            (when-not shape
                              (m/fail "Protected export target requires trusted ABI signature" {:name n}))
                            (when-not (= (count (:params (get old n))) (count (:params shape)))
                              (m/fail "Protected export target ABI arity mismatch" {:name n}))
                            ;; Only this shape is used by ABI redirect validation;
                            ;; existing executable code remains the old function.
                            {:kind "decl" :name n :ir {:fdecl {:f n :type (:return-type shape)
                                                              :xs (mapv (fn [i p] (assoc p :x {:idx i}))
                                                                        (range) (:params shape))}}})
                          (reader n)))
         alias-catalogue {:manifests (into (vec (:manifests catalogue)) (:manifests candidate))
                          :declarations {} :read-declaration alias-reader}
         _ (doseq [n (keys (:declarations candidate))]
             (name! n)
             (let [row (read-row candidate n)]
               (when (and (:sourceLocal row) (contains? protected n))
                 (m/fail "Compiled declaration overwrites protected name" {:name n}))))
         _ (doseq [n (:missingDependencies manifest)]
             (when-not (or (contains? old n) (= "decl" (:kind (reader n))))
               (m/fail "Unresolved compiled missing dependency" {:name n})))
         entries (:entryPoints manifest)
         _ (when-not (and (= (count entries) (count (set (map :name entries))))
                          (= (count (:requestedRoots manifest)) (count (set (:requestedRoots manifest)))))
             (m/fail "Duplicate compiled entry point" {}))
         _ (when-not (= (set (:requestedRoots manifest)) (set (map :name entries)))
             (m/fail "Compiled entry point roots mismatch" {}))
         _ (doseq [{:keys [name boxedTarget]} entries]
             (name! name) (name! boxedTarget)
             (let [wrapper ["str" name "_boxed"]
                   expected (if (= "decl" (:kind (read-row candidate wrapper))) wrapper name)]
               (when-not (= expected boxedTarget)
                 (m/fail "Compiled boxed entry point name mismatch" {:name name :boxed-target boxedTarget :expected expected})))
             (when-not (and (:sourceLocal (read-row candidate name))
                            (:sourceLocal (read-row candidate boxedTarget))
                            (not (contains? protected name)) (not (contains? protected boxedTarget)))
               (m/fail "Compiled entry point must be a new local declaration" {:name name})))
         roots (into (into (vec (:requestedRoots manifest)) (map :boxedTarget entries)) action-roots)
         new-functions
         (loop [pending roots new {} visited-old #{}]
           (if (empty? pending) new
             (let [name (peek pending) pending (pop pending)]
               (cond
                 (or (contains? new name) (contains? visited-old name)) (recur pending new visited-old)
                 (contains? old name) (recur pending new (conj visited-old name))
                 (contains? protected name) (m/fail "Compiled dependency uses reserved unavailable name" {:name name})
                 :else
                 (let [row (reader name)
                       decl (declaration! row)
                       _ (when-not (= name (:name row)) (m/fail "Compiled dependency name mismatch" {:name name}))
                       [actual f] (if (get-in row [:ir :extern])
                                    (or (when lower-extern (lower-extern row))
                                      (if research-traps?
                                      ;; Only unknown externs may trap; malformed supported ABIs
                                      ;; and missing/invalid redirect targets still throw.
                                      (abi/lower-deferred-catalogue alias-catalogue row)
                                      (abi/lower-catalogue alias-catalogue row)))
                                    (ir/lower-declaration row))
                       _ (when-not (= name actual) (m/fail "Compiled lowered name mismatch" {:name name :actual actual}))
                       f (with-signature f decl)
                       dependencies (cond-> (into (body-dependencies (:body f)) (:runtime-dependencies f))
                                      (:runtime-initializer f) (conj (:runtime-initializer f)))]
                   (recur (into pending dependencies) (assoc new name f) visited-old))))))
         all (merge old new-functions)
         _ (doseq [{:keys [action]} (:actions plan)]
             (when (and (= "initialize" (:kind action))
                        (not= (:target action) (:runtime-initializer (get all (:name action)))))
               (m/fail "Compiled initialized-global target mismatch" {:action action})))
         _ (validate-calls! new-functions all)
         _ (doseq [{:keys [name boxedTarget]} entries]
             (when-not (= (count (:params (get all name))) (count (:params (get all boxedTarget))))
               (m/fail "Compiled boxed entry point arity mismatch" {:name name :boxed-target boxedTarget})))
         reserved (into protected (keys (:declarations candidate)))
         functions (wrap-new-globals old new-functions (:globals world) reserved)
         [functions pending]
         (reduce
          (fn [[functions pending] {:keys [action] :as planned}]
            (when-not (map? action) (m/fail "Malformed compiled initializer action" {}))
            (let [key (if (= "io" (:kind action))
                        [:prototype.initialization/io (:name action)] (:name action))
                  present? (contains? (:globals world) key)
                  ready? (= :ready (get-in world [:globals key :status]))]
              (when (and present? (not ready?))
                (m/fail "Compiled action has incomplete prior initialization" {:action action :key key}))
            (if (or (contains? completed-local-actions action) ready?)
              [functions pending]
              (let [kind (:kind action) name (:name action)
                    _ (name! name)
                    target (case kind
                             "value" name
                             "initialize" (or (get-in functions [name :init-target])
                                              (m/fail "Compiled initializer has no global target" {:name name}))
                             "io" ["str" name "_ansatz_io_initializer"])
                    functions (if (= "io" kind)
                                (do (when (or (contains? functions target) (contains? (:globals world) target) (contains? reserved target))
                                      (m/fail "Compiled synthetic IO name collision" {:name name}))
                                    (assoc functions target {:params [] :body [:begin-init [:prototype.initialization/io name] (:target action)
                                                                              (initializer-arguments functions (:target action)) "object"]}))
                                functions)]
                (when-not (and (get functions target) (empty? (:params (get functions target))))
                  (m/fail "Compiled initializer action target arity mismatch" {:name name :target target}))
                [functions (conj pending (assoc planned :call-target target :completion-key action))]))))
          [functions []] (:actions plan))]
     {:world (assoc world :functions functions)
      :boxed-entrypoints (into {} (map (juxt :name :boxedTarget)) entries)
      :pending-local-initializers pending
      :new-functions (select-keys functions (remove #(contains? old %) (keys functions)))
      :initialization-plan plan :manifest manifest})))

(defn install-at-host-boundary
  "Admit new code while the guest is stopped at an explicit host callback.
  Preserves the entire continuation. Existing declarations remain protected by
  install; no active frame or closure can be redirected. The raw interop driver
  must adopt the returned immutable program before resuming or invoking helpers.
  Initialization remains explicit in :pending-local-initializers."
  ([world bundle] (install-at-host-boundary world bundle {}))
  ([world bundle options]
   (when-not (and (= :host-call (:status world)) (map? (:host-request world)))
     (m/fail "Compiled continuation installation requires a host callback boundary" {:status (:status world)}))
   (let [result (install (assoc world :status :done) bundle options)]
     (update result :world assoc :status :host-call))))
