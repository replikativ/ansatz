(ns prototype.import-ir
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.scalar :as scalar]
            [prototype.machine :as m]))

(defn name-label [[op parent part]]
  (case op "anonymous" "" (let [p (name-label parent)] (str p (when (seq p) ".") part))))

(defn operand [a]
  (cond (= a "erased") [:imm m/erased]
        (:var a) [:var (get-in a [:var :id :idx])]
        :else (m/fail "Unknown imported operand" {:operand a})))

(defn layout! [i]
  (when-not (and (map? i) (every? #(and (integer? %) (<= 0 % 1048576)) (map i [:size :usize :ssize]))
                 (< (:size i) 256) (< (+ (* 8 (:usize i)) (:ssize i)) 1024))
    (m/fail "Invalid constructor layout" {:layout i})))

(defn type! [ty]
  (when-not (contains? #{"erased" "object" "tobject" "tagged" "void" "uint8" "uint16" "uint32" "uint64" "usize"} ty)
    (m/fail "Unsupported imported runtime type" {:type ty})))

(defn expression
  ([e] (expression e nil))
  ([e target-type]
  (let [[op data] (first e)]
    (case op
      :ctor (do (layout! (:i data))
                (when-not (= (count (:ys data)) (get-in data [:i :size]))
                  (m/fail "Constructor field count mismatch" {:constructor data}))
                (let [{:keys [size usize ssize cidx]} (:i data) fields (mapv operand (:ys data))]
                  (if (pos? (+ usize ssize))
                    [:scalar-ctor cidx fields {:objects size :usize usize :ssize ssize}]
                    [:ctor cidx fields])))
      :proj [:project [:var (get-in data [:x :idx])] (:i data)]
      :uproj [:scalar-get [:var (get-in data [:x :idx])] {:index (:i data) :offset 0 :type "usize" :region :usize}]
      :sproj (do (scalar/width target-type)
                 [:scalar-get [:var (get-in data [:x :idx])]
                  {:index (:n data) :offset (:offset data) :type target-type :region :scalar}])
      :box (do (scalar/width (:ty data)) [:box (:ty data) [:var (get-in data [:x :idx])]])
      :unbox (do (scalar/width target-type) [:unbox target-type [:var (get-in data [:x :idx])]])
      :isShared [:shared? [:var (get-in data [:x :idx])]]
      :fap [:invoke [:direct (:c data)] (mapv operand (:ys data))]
      :pap [:closure (:c data) (mapv operand (:ys data))]
      :ap [:invoke [:closure [:var (get-in data [:x :idx])]] (mapv operand (:ys data))]
      :lit [:literal (or (get-in data [:v :num :v]) (get-in data [:v :str :v]))]
      (m/fail "Unsupported imported expression" {:expression e})))))

(declare body)
(defn alternative [[op a b]]
  (case op "ctor" [(:cidx a) (body b)] "default" [:default (body a)]
        (m/fail "Unknown alternative" {:op op})))

(defn body [[op a b c d e f]]
  (case op
    "vdecl" (let [_ (type! b) x (:idx a) expr (expression c b) continuation (body d)]
              (if (= :invoke (first expr))
                (if (= continuation [:return [:var x]])
                  [:tail (second expr) (nth expr 2)]
                  [:call x (second expr) (nth expr 2) continuation])
                [:let x expr continuation]))
    "jdecl" [:join (:idx a) (mapv #(get-in % [:x :idx]) b) (body c) (body d)]
    "jmp" [:jump (:idx a) (mapv operand b)]
    "case" [:case [:var (:idx b)] (mapv alternative d)]
    "ret" [:return (operand a)]
    "inc" (if d (m/fail "Persistent RC flag unsupported" {}) [:inc [:var (:idx a)] b (body e)])
    "dec" (if d (m/fail "Persistent RC flag unsupported" {}) [:dec [:var (:idx a)] b (body e)])
    "set" [:set [:var (:idx a)] b (operand c) (body d)]
    "uset" [:scalar-set [:var (:idx a)] {:index b :offset 0 :type "usize" :region :usize} [:var (:idx c)] (body d)]
    "sset" (do (scalar/width e)
               [:scalar-set [:var (:idx a)] {:index b :offset c :type e :region :scalar} [:var (:idx d)] (body f)])
    (m/fail "Unsupported imported instruction" {:op op})))

(defn validate-manifest! [manifest]
  (when-not (and (= "lean-ir-probe/1" (:schema manifest)) (= "4.33.1" (:leanVersion manifest)))
    (m/fail "Unsupported producer" {:manifest manifest}))
  ;; Historical object-only fixtures predate explicit platform metadata. The
  ;; scalar representation is intentionally the tested x86-64 profile only.
  (when-let [profile (:runtimeProfile manifest)]
    (when-not (and (= 64 (:wordBits profile)) (string? (:target profile))
                   (str/starts-with? (:target profile) "x86_64-"))
      (m/fail "Unsupported runtime profile" {:profile profile})))
  manifest)

(defn- rows [path]
  (let [rows (mapv #(json/read-str % :key-fn keyword :bigdec false) (str/split-lines (slurp path)))]
    (validate-manifest! (first rows))
    rows))

(defn lower-declaration [row]
  (let [f (get-in row [:ir :fdecl])]
    (when-not f (m/fail "Missing body or extern" {:name (:name row)}))
    (type! (:type f))
    (doseq [p (:xs f)] (type! (:ty p)))
    [(:f f) {:params (mapv #(get-in % [:x :idx]) (:xs f)) :body (body (:body f))}]))

(defn- check-function-profile! [manifests row function]
  ;; The raw lowering function is also used by static audits. Executable bundle
  ;; loading additionally requires explicit ABI provenance for the new scalar
  ;; forms. Conservatively reject mixed legacy/profiled catalogues here.
  (let [decl (or (get-in row [:ir :fdecl]) (get-in row [:ir :extern]))
        sensitive? (or (some #{"uint32" "uint64" "usize"} (cons (:type decl) (map :ty (:xs decl))))
                       (some #(and (vector? %) (contains? #{:scalar-ctor :scalar-get :scalar-set :box :unbox} (first %)))
                             (tree-seq coll? seq (:body function))))]
    (when sensitive?
      (when (or (empty? manifests) (some #(nil? (:runtimeProfile %)) manifests))
        (m/fail "Scalar execution requires explicit runtime profile" {:name (:name row)}))
      (doseq [manifest manifests] (validate-manifest! manifest)))))

(defn load-bundle [path]
  (let [rows (rows path)]
    (into {} (map (fn [row]
                    (let [[name function :as pair] (lower-declaration row)]
                      (check-function-profile! [(first rows)] row function) pair)) (rest rows)))))

(defn index-bundles [paths]
  ;; JSON decoding is still eager. This is a raw declaration catalogue, not
  ;; admission of every indexed body to the executable subset.
  (reduce (fn [catalogue path]
            (let [rows (rows path)]
              (reduce (fn [catalogue row]
                        (let [name (:name row)]
                          (when-not name (m/fail "Missing declaration name" {:path path}))
                          (when-let [old (get-in catalogue [:declarations name])]
                            (when-not (= (select-keys old [:kind :ir :dependencies])
                                         (select-keys row [:kind :ir :dependencies]))
                              (m/fail "Conflicting declaration" {:name name})))
                          (assoc-in catalogue [:declarations name] row)))
                      (update catalogue :manifests conj (first rows)) (rest rows))))
          {:manifests [] :declarations {}} paths))

(defn- static-targets [[op a b c d]]
  (case op
    :let (cond-> (static-targets c) (= :closure (first b)) (conj (second b)))
    :call (cond-> (static-targets d) (= :direct (first b)) (conj (second b)))
    :tail (if (= :direct (first a)) #{(second a)} #{})
    :join (into (static-targets c) (static-targets d))
    :case (into #{} (mapcat #(static-targets (second %)) b))
    (:inc :dec) (static-targets c)
    (:set :scalar-set) (static-targets d)
    :suspend (static-targets b)
    :host (static-targets d)
    (:return :jump) #{}))

(defn load-closure
  ([catalogue roots] (load-closure catalogue roots lower-declaration))
  ([catalogue roots lower]
  (loop [pending (vec roots) functions {}]
    (if (empty? pending) functions
      (let [name (peek pending) pending (pop pending)]
        (if (contains? functions name) (recur pending functions)
          (let [row (or (if-let [read-declaration (:read-declaration catalogue)]
                         (read-declaration name)
                         (get-in catalogue [:declarations name]))
                        (m/fail "Missing declaration dependency" {:name name}))
                [actual function] (lower row)]
            (when-not (= name actual) (m/fail "Declaration name mismatch" {:name name :actual actual}))
            (check-function-profile! (:manifests catalogue) row function)
            ;; Derive dependencies from the admitted body, rather than trusting
            ;; optional producer dependency metadata.
            (recur (into pending (static-targets (:body function))) (assoc functions name function)))))))))
