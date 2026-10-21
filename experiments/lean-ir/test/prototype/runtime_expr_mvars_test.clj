(ns prototype.runtime-expr-mvars-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.runtime-expr-mvars :as runtime]
            [prototype.runtime-expr-transform :as transform]
            [prototype.runtime-expr :as expr]
            [prototype.runtime-mvars :as levels]
            [prototype.runtime-prim :as prim]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.scalar :as scalar]))

(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release :replace-node m/replace-node})
(def root ["str" ["str" ["anonymous"] "Lean"] "instantiateExprMVarsImp"])
(defn- cached [world tag fields data & [annotation]]
  (let [[world ref] (m/allocate world :ctor tag fields)
        layout {:objects (count fields) :usize 0 :ssize (if (nil? annotation) 8 9)}
        bytes (scalar/write-bytes layout {} {:index (count fields) :offset 0 :type "uint64" :region :scalar} data)
        bytes (if (nil? annotation) bytes
                (scalar/write-bytes layout bytes {:index (count fields) :offset 8 :type "uint8" :region :scalar} annotation))]
    [(update-in world [:heap (:id ref)] assoc :layout layout :scalar-bytes bytes) ref]))
(defn- make-name [world n] (cached world 1 [0 (:name n)] (bigint (:hash n))))
(declare make-expr)
(defn- make-level [world encoded cache]
  (let [key [:level (or (:id encoded) encoded)]]
    (if-let [ref (get @cache key)] [(m/retain world ref 1) ref]
      (let [[op & args] (:tree encoded)]
        (if (= op "zero") [world 0]
          (let [[world fields] (if (contains? #{"param" "mvar"} op)
                                 (let [[world name] (make-name world (first args))] [world [name]])
                                 (reduce (fn [[world fs] l] (let [[world l] (make-level world l cache)]
                                                            [world (conj fs l)])) [world []] args))
                [world ref] (cached world ({"succ" 1 "max" 2 "imax" 3 "param" 4 "mvar" 5} op)
                                    fields (bigint (:data encoded)))]
            (swap! cache assoc key ref) [world ref]))))))
(defn- make-list [world encoded cache]
  (reduce (fn [[world tail] head]
            (let [[world head] (make-level world head cache)] (m/allocate world :ctor 1 [head tail])))
          [world 0] (rseq (vec encoded))))
(defn- make-expr [world encoded cache]
  (let [key [:expr (or (:id encoded) encoded)]]
    (if-let [ref (get @cache key)] [(m/retain world ref 1) ref]
      (let [[op & args] (:tree encoded)
            [world fields annotation]
            (case op
              "bvar" [world [(bigint (first args))] nil]
              ("fvar" "mvar") (let [[world name] (make-name world (first args))] [world [name] nil])
              "sort" (let [[world l] (make-level world (first args) cache)] [world [l] nil])
              "const" (let [[world name] (make-name world (first args))
                            [world ls] (make-list world (second args) cache)] [world [name ls] nil])
              "app" (let [[world f] (make-expr world (first args) cache)
                          [world a] (make-expr world (second args) cache)] [world [f a] nil])
              ("lam" "forall") (let [[world name] (make-name world (nth args 0))
                                     [world d] (make-expr world (nth args 1) cache)
                                     [world b] (make-expr world (nth args 2) cache)] [world [name d b] (nth args 3)])
              "let" (let [[world name] (make-name world (nth args 0))
                          [world t] (make-expr world (nth args 1) cache)
                          [world v] (make-expr world (nth args 2) cache)
                          [world b] (make-expr world (nth args 3) cache)] [world [name t v b] (if (nth args 4) 1 0)])
              ("nat" "string") (let [[world lit] (m/allocate world :ctor (if (= op "nat") 0 1)
                                                            [(if (= op "nat") (bigint (first args)) (first args))])]
                                   [world [lit] nil])
              "mdata" (let [[world metadata] (m/allocate world :ctor 0 [0])
                            [world e] (make-expr world (first args) cache)] [world [metadata e] nil])
              "proj" (let [[world name] (make-name world (nth args 0))
                           [world e] (make-expr world (nth args 2) cache)] [world [name (bigint (nth args 1)) e] nil]))
            tag ({"bvar" 0 "fvar" 1 "mvar" 2 "sort" 3 "const" 4 "app" 5 "lam" 6 "forall" 7
                  "let" 8 "nat" 9 "string" 9 "mdata" 10 "proj" 11} op)
            [world ref] (cached world tag fields (bigint (:data encoded)) annotation)]
        (swap! cache assoc key ref) [world ref]))))
(defn- scalar [node offset type]
  (scalar/read-bytes (:layout node) (:scalar-bytes node)
                     {:index (count (:fields node)) :offset offset :type type :region :scalar}))
(defn- encode-name [world value]
  (let [n (m/node world value)] {:name (second (:fields n)) :hash (str (scalar n 0 "uint64"))}))
(declare encode-expr)
(defn- encode-level [world value]
  (if (integer? value) {:tree ["zero"] :data "2221"}
    (let [n (m/node world value) fs (:fields n)]
      {:tree (case (:tag n) 1 ["succ" (encode-level world (first fs))]
                   2 ["max" (encode-level world (first fs)) (encode-level world (second fs))]
                   3 ["imax" (encode-level world (first fs)) (encode-level world (second fs))]
                   4 ["param" (encode-name world (first fs))]
                   5 ["mvar" (encode-name world (first fs))])
       :data (str (scalar n 0 "uint64"))})))
(defn- encode-list [world value]
  (loop [x value out []]
    (if (integer? x) out
      (let [[head tail] (:fields (m/node world x))] (recur tail (conj out (encode-level world head)))))))
(defn- encode-expr [world value]
  (let [n (m/node world value) f (:fields n)
        tree (case (:tag n)
               0 ["bvar" (str (first f))]
               (1 2) [(if (= 1 (:tag n)) "fvar" "mvar") (encode-name world (first f))]
               3 ["sort" (encode-level world (first f))]
               4 ["const" (encode-name world (first f)) (encode-list world (second f))]
               5 ["app" (encode-expr world (first f)) (encode-expr world (second f))]
               (6 7) [(if (= 6 (:tag n)) "lam" "forall") (encode-name world (nth f 0))
                      (encode-expr world (nth f 1)) (encode-expr world (nth f 2)) (scalar n 8 "uint8")]
               8 ["let" (encode-name world (nth f 0)) (encode-expr world (nth f 1))
                  (encode-expr world (nth f 2)) (encode-expr world (nth f 3)) (= 1 (scalar n 8 "uint8"))]
               9 (let [lit (m/node world (first f)) v (first (:fields lit))]
                   [(if (= 0 (:tag lit)) "nat" "string") (if (= 0 (:tag lit)) (str v) v)])
               10 ["mdata" (encode-expr world (second f))]
               11 ["proj" (encode-name world (nth f 0)) (str (nth f 1)) (encode-expr world (nth f 2))])]
    {:tree tree :data (str (scalar n 0 "uint64"))}))

(defn- name-text [world name] (second (:fields (m/node world name))))
(defn- lookup-handler [table]
  (fn [_ world [ctx name]]
    (let [array (nth (:fields (m/node world ctx)) table) entries (:fields (m/node world array))
          found (first (filter #(= (name-text world name) (name-text world (first %))) (partition 2 entries)))
          world (if found (m/retain world (second found) 1) world)
          world (-> world (m/release ctx 1) (m/release name 1))]
      (if found (m/allocate world :ctor 1 [(second found)]) [world 0]))))
(defn- assign-handler [table]
  (fn [_ world [ctx name value]]
    (let [tables (:fields (m/node world ctx)) entries (:fields (m/node world (nth tables table)))
          kept (vec (mapcat identity (remove #(= (name-text world name) (name-text world (first %))) (partition 2 entries))))
          world (reduce #(m/retain %1 %2 1) world kept)
          [world array] (m/allocate world :array 246 (into kept [name value]))
          world (reduce #(m/retain %1 %2 1) world (keep-indexed #(when (not= table %1) %2) tables))
          world (m/release world ctx 1)]
      (m/allocate world :ctor 0 (assoc (vec tables) table array)))))
(defn- app-owned [world f a]
  (let [data (mapv #(scalar (m/node world %) 0 "uint64") [f a])
        cache (second (expr/evaluate ops world "lean_expr_mk_app_data" data))]
    (cached (m/retain world a 1) 5 [f a] cache)))
(defn- beta-handler [_ world [function array zeta preserve]]
  ;; Independent transcription of guest Expr.betaRev's control flow. Pure
  ;; deBruijn transforms are independently native-oracle-tested by that module.
  (let [args (:fields (m/node world array)) sz (count args)]
    (if (zero? sz) [world function]
      (loop [world world e function i 0]
        (let [node (m/node world e) fs (:fields node)]
          (cond
            (= 6 (:tag node))
            (if (< (inc i) sz)
              (recur (-> world (m/retain (nth fs 2) 1) (m/release e 1)) (nth fs 2) (inc i))
              (let [[world result] (transform/evaluate ops world "lean_expr_instantiate" [(nth fs 2) array])]
                [(m/release world e 1) result]))
            (and (= 8 (:tag node)) (= 1 zeta) (< i sz))
            (let [[world result] (transform/evaluate ops world "lean_expr_instantiate1" [(nth fs 3) (nth fs 2)])]
              (recur (m/release world e 1) result i))
            (and (= 10 (:tag node)) (zero? preserve))
            (recur (-> world (m/retain (nth fs 1) 1) (m/release e 1)) (nth fs 1) i)
            :else
            (let [n (- sz i) [world e2] (transform/evaluate ops world "lean_expr_instantiate_range" [e n sz array])
                  world (m/release world e 1)]
              (reduce (fn [[world e] index] (app-owned world e (nth args index))) [world e2] (reverse (range n))))))))))
(defn- extern-row [name symbol borrow]
  {:kind "decl" :name name :ir {:extern {:f name :xs (mapv (fn [i ty borrowed] {:x {:idx (inc i)} :ty ty :borrow borrowed})
                                                          (range) (case name
                                                                    ["unused"] []
                                                                    (cond (= name runtime/beta) ["object" "object" "uint8" "uint8"]
                                                                          (= name runtime/lift) ["object" "tobject" "tobject"]
                                                                          (= name levels/setter) ["object" "tobject" "tobject"]
                                                                          (= 3 (count borrow)) ["object" "tobject" "object"]
                                                                          :else ["object" "tobject"])) borrow)
                                        :type (if (contains? #{runtime/getter runtime/delayed-getter levels/getter} name) "tobject" "object")
                                        :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}})
(def binding-info
  [[runtime/getter "test_expr_get" (lookup-handler 0)]
   [runtime/setter "test_expr_assign" (assign-handler 0)]
   [runtime/delayed-getter "test_delayed_get" (lookup-handler 2)]
   [levels/getter "test_level_get" (lookup-handler 1)]
   [levels/setter "test_level_assign" (assign-handler 1)]
   [runtime/beta "test_beta" beta-handler]
   [runtime/lift "test_lift" (fn [_ world args] (transform/evaluate ops world "lean_expr_lift_loose_bvars" args))]])
(def bindings
  (into {} (map (fn [[name symbol handler]]
                  (let [spec (first (filter #(= name (:target %)) (vals runtime/requests)))
                        row (extern-row name symbol (:borrow spec)) ext (get-in row [:ir :extern])]
                    [symbol {:signature {:params (mapv #(select-keys % [:ty :borrow]) (:xs ext)) :return-type (:type ext)}
                             :handler handler}])) binding-info)))
(def functions
  (into {root {:params [1 2] :body (runtime/body [1 2] 3)}}
        (map (fn [[name symbol _]]
               (let [spec (first (filter #(= name (:target %)) (vals runtime/requests)))]
                 (raw/lower bindings (extern-row name symbol (:borrow spec))))) binding-info)))
(defn with-runtime [f]
  (let [base prim/evaluate]
    (with-redefs [prim/evaluate (fn [ops world symbol args]
                                 (if (or (contains? runtime/supported-symbols symbol)
                                         (contains? runtime/internal-symbols symbol))
                                   (runtime/evaluate ops world symbol args) (base ops world symbol args)))]
      (f))))
(defn cases [] (mapv #(json/read-str % :key-fn keyword) (str/split-lines (slurp "fixtures/instantiate-expr-mvars-native.jsonl"))))
(defn- prepare [case]
  (let [cache (atom {})
        ;; The oracle uses flat string Names; build their exact cache too.
        names (into {} (keep (fn [x] (when (and (map? x) (:name x) (:hash x)) [(:name x) x])))
                    (tree-seq coll? seq case))
        table (fn [world entries build]
                (let [[world values] (reduce (fn [[world out] [name value]]
                                              (let [[world name] (make-name world (get names name))
                                                    [world value] (build world value)] [world (into out [name value])] ))
                                            [world []] entries)]
                  (m/allocate world :array 246 values)))
        [world es] (table (m/world functions) (:assignments case) #(make-expr %1 %2 cache))
        [world ls] (table world (:levelAssignments case) #(make-level %1 %2 cache))
        delayed-entries (mapv (fn [[name [xs pending]]] [name [xs pending]]) (:delayed case))
        [world ds] (table world delayed-entries
                         (fn [world [xs pending]]
                           (let [[world fvars] (reduce (fn [[world out] x]
                                                        (let [[world x] (make-expr world x cache)]
                                                          [world (conj out x)])) [world []] xs)
                                 [world fvars] (m/allocate world :array 246 fvars)
                                 [world pending] (make-name world (get names pending))]
                             (m/allocate world :ctor 0 [fvars pending]))))
        [world ctx] (m/allocate world :ctor 0 [es ls ds])
        [world input] (make-expr world (:input case) cache)]
    [(-> world (m/retain ctx 1) (m/retain input 1)) ctx input]))

(defn- semantic [value]
  (cond (map? value) (into {} (map (fn [[k v]] [k (semantic v)])) (dissoc value :id))
        (vector? value) (mapv semantic value)
        :else value))
(defn- encoded-table [world ctx index encode]
  (into {} (map (fn [[name value]] [(name-text world name) (encode world value)]))
        (partition 2 (:fields (m/node world (nth (:fields (m/node world ctx)) index))))))

(deftest native-differential-two-pass-instantiation
  (with-runtime
    (fn []
      (let [sessions (into {} (map (fn [backend] [backend (raw/open-functions functions bindings {:backend backend})]))
                           [:reference :mutable :jvm])]
      (doseq [case (cases) backend [:reference :mutable :jvm]]
        (let [[parent context input] (prepare case)
              result (raw/call (get sessions backend) parent root [context input])
              world (:state result) [ctx output] (:fields (m/node world (:value result)))
              original-node (m/node world input) output-node (m/node world output)
              prefix-shared (and (= 5 (:tag original-node)) (= 5 (:tag output-node))
                                 (= (first (:fields original-node)) (first (:fields output-node))))
              app-shared (and (= 5 (:tag output-node)) (apply = (:fields output-node)))]
          (is (= (semantic (:result case)) (encode-expr world output)) (str (:label case) " " backend))
          (is (= (semantic (into {} (:finalAssignments case))) (encoded-table world ctx 0 encode-expr)) (:label case))
          (is (= (semantic (into {} (:finalLevelAssignments case))) (encoded-table world ctx 1 encode-level)) (:label case))
          (is (= (:sameContext case) (= context ctx)) (:label case))
          (is (= (:sameExpr case) (= input output)) (:label case))
          (is (= (:prefixShared case) (boolean prefix-shared)) (:label case))
          (is (= (:appShared case) (boolean app-shared)) (:label case))
          (is (not-any? #(or (:expr-mvars-work %) (:level-mvars-work %)) (vals (:heap world))))
          (is (= (semantic (:input case)) (encode-expr parent input)))
          (is (empty? (:heap (-> world (m/release (:value result) 1) (m/release context 1) (m/release input 1)))) (:label case))))))))

(deftest paused-direct-and-delayed-instantiation-resumes-in-independent-forks
  (with-runtime
    (fn []
      (let [sessions (into {} (map (fn [backend] [backend (raw/open-functions functions bindings {:backend backend})]))
                           [:reference :mutable :jvm])
            chosen (filter #(contains? #{"chain writeback" "delayed binder lift" "delayed reentered scopes"
                                         "delayed unresolved cut writeback" "level sorts"} (:label %)) (cases))]
        (doseq [case chosen backend [:reference :mutable :jvm] budget [0 1 7 15 31 63 127]]
          (let [[parent context input] (prepare case) session (assoc (get sessions backend) :fuel budget)
                checkpoint (try (:state (raw/call session parent root [context input]))
                                (catch clojure.lang.ExceptionInfo error (:checkpoint (ex-data error))))
                session (assoc session :fuel 100000)
                a (raw/continue session checkpoint) b (raw/continue session checkpoint)
                world (:state a) [ctx output] (:fields (m/node world (:value a)))]
            (is (= (:state a) (:state b)) (str (:label case) " " backend " fuel " budget))
            (is (= (semantic (:result case)) (encode-expr world output)))
            (is (= (semantic (into {} (:finalAssignments case))) (encoded-table world ctx 0 encode-expr)))
            (is (not-any? #(or (:expr-mvars-work %) (:level-mvars-work %)) (vals (:heap world))))
            (is (empty? (:heap (-> world (m/release (:value a) 1) (m/release context 1) (m/release input 1)))))
            (is (= (semantic (:input case)) (encode-expr parent input)))))))))
