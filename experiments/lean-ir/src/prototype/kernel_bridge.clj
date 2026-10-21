(ns prototype.kernel-bridge
  "Checking projection from pinned Lean guest constructors to Ansatz Java values.
   Never replaces guest objects. Cached Lean data/hashes are validated as storage
   but recomputed by Java. mdata is erased, letE.nondep is checked then omitted,
   and raw universe max/imax may normalize. This is not a frontend round trip.
   Default projections have fresh memos; an explicit world-scoped projector can
   share one memo during a bulk import. All traversals use an explicit stack."
  (:require [prototype.machine :as m]
            [prototype.scalar :as scalar]
            [prototype.constructor-layout :as constructor]
            [prototype.native-scalar :as native]
            [prototype.runtime-string :as string])
  (:import [ansatz.kernel Name Level Expr ConstantInfo Env TypeChecker]
           [java.util HashMap]))

(defn- fail [message data] (throw (ex-info message data)))
(def ^:private carrier-ops {:ref? m/ref? :node m/node})
(defn- nat! [world value] (native/nat-value carrier-ops world value))
(defn- long! [world value]
  (let [n (nat! world value)]
    (when (> n Long/MAX_VALUE) (fail "Guest Nat exceeds Java long representation" {:value value})) (long n)))
(defn- scalar-tag [v]
  (cond (native/native-scalar? v) (native/payload v)
        (integer? v) (long! nil v) (instance? prototype.machine.Tag v) (:tag v) :else nil))

(defn constructor-layout?
  "Pinned semantic storage, or validated native/imported raw clone padding.
   Storage witnesses never establish native object or kernel identity."
  [node fields scalar-size]
  (constructor/constructor-layout? node fields scalar-size))
(defn- ctor! [world value tag fields scalar-size]
  (when-not (m/ref? value) (fail "Expected guest constructor reference" {:value value}))
  (let [node (m/node world value)
        layout (:layout node)]
    (when-not (and (= :ctor (:kind node)) (= tag (:tag node)) (vector? (:fields node))
                   (= fields (count (:fields node)))
                   (constructor-layout? node fields scalar-size))
      (fail "Invalid pinned guest constructor layout" {:value value :node node :expected [tag fields scalar-size]}))
    ;; Ignore computed-cache content semantically, but reject missing bytes.
    (doseq [i (range scalar-size)]
      (scalar/read-bytes layout (:scalar-bytes node)
        {:index fields :offset i :type "uint8" :region :scalar}))
    node))
(defn- byte-at [node offset]
  (scalar/read-bytes (:layout node) (:scalar-bytes node)
    {:index (count (:fields node)) :offset offset :type "uint8" :region :scalar}))
(defn- leaf [value] {:children [] :build (fn [_] value)})

(defn- specification [world kind value]
  (case kind
    :nat (leaf (nat! world value))
    :string (leaf (string/string-value carrier-ops world value))
    :name
    (if (= 0 (scalar-tag value)) (leaf Name/ANONYMOUS_NAME)
      (let [tag (:tag (m/node world value)) node (ctor! world value tag 2 8) [parent payload] (:fields node)]
        (case tag
          1 {:children [[:name parent] [:string payload]] :build (fn [[p s]] (Name/mkStr p s))}
          2 {:children [[:name parent]] :build (fn [[p]] (Name/mkNum p (long! world payload)))}
          (fail "Invalid guest Name tag" {:tag tag}))))
    :level
    (if (= 0 (scalar-tag value)) (leaf Level/ZERO_LEVEL)
      (let [tag (:tag (m/node world value))
            _ (when (= 5 tag) (fail "Unresolved guest level metavariable" {}))
            count (case tag 1 1 (2 3) 2 4 1 (fail "Invalid guest Level tag" {:tag tag}))
            node (ctor! world value tag count 8) [a b] (:fields node)]
        (case tag
          1 {:children [[:level a]] :build (fn [[a]] (Level/succ a))}
          2 {:children [[:level a] [:level b]] :build (fn [[a b]] (Level/max a b))}
          3 {:children [[:level a] [:level b]] :build (fn [[a b]] (Level/imax a b))}
          4 {:children [[:name a]] :build (fn [[a]] (Level/param a))})))
    (:names :levels)
    (if (= 0 (scalar-tag value)) (leaf '())
      (let [[head tail] (:fields (ctor! world value 1 2 0))]
        {:children [[(if (= kind :names) :name :level) head] [kind tail]] :build (fn [[head tail]] (cons head tail))}))
    :literal
    (let [tag (:tag (m/node world value)) [payload] (:fields (ctor! world value tag 1 0))]
      (case tag
        0 {:children [[:nat payload]] :build (fn [[n]] (Expr/litNat n))}
        1 {:children [[:string payload]] :build (fn [[s]] (Expr/litStr s))}
        (fail "Invalid guest Literal tag" {:tag tag})))
    :expr
    (let [tag (:tag (m/node world value))
          _ (when (contains? #{1 2} tag) (fail "Unresolved guest free/metavariable" {:tag tag}))
          [fields size] (case tag (0 3 9) [1 8] (4 5 10) [2 8] (6 7) [3 9] 8 [4 9] 11 [3 8]
                         (fail "Invalid guest Expr tag" {:tag tag}))
          node (ctor! world value tag fields size) [a b c d] (:fields node)]
      (case tag
        0 (let [idx (long! world a)]
            (when (>= idx 1048575) (fail "Guest bound variable exceeds Java metadata range" {:index idx}))
            (leaf (Expr/bvar idx)))
        3 {:children [[:level a]] :build (fn [[u]] (Expr/sort u (Level/hasParam u)))}
        4 {:children [[:name a] [:levels b]]
           :build (fn [[n levels]] (Expr/mkConst n (object-array levels) (boolean (some #(Level/hasParam %) levels))))}
        5 {:children [[:expr a] [:expr b]] :build (fn [[f x]] (Expr/app f x))}
        (6 7) (let [info (byte-at node 8)]
                (when-not (< info 4) (fail "Invalid guest BinderInfo" {:value info}))
                {:children [[:name a] [:expr b] [:expr c]]
                 :build (fn [[n t body]]
                          (let [bi (nth [:default :implicit :strict-implicit :inst-implicit] info)]
                            (if (= tag 6) (Expr/lam n t body bi) (Expr/forall n t body bi))))})
        8 (do (when-not (< (byte-at node 8) 2) (fail "Invalid guest nondep Bool" {}))
              {:children [[:name a] [:expr b] [:expr c] [:expr d]]
               :build (fn [[n t v body]] (Expr/mkLet n t v body))})
        9 {:children [[:literal a]] :build first}
        10 {:children [[:expr b]] :build first}
        11 {:children [[:name a] [:expr c]] :build (fn [[n e]] (Expr/proj n (long! world b) e))}))
    :constant-val
    (let [[name params type] (:fields (ctor! world value 0 3 0))]
      {:children [[:name name] [:names params] [:expr type]]
       :build (fn [[n p t]] {:name n :params p :type t})})
    :hints
    (case (scalar-tag value)
      0 (leaf ConstantInfo/REDUCIBILITY_OPAQUE)
      1 (leaf ConstantInfo/REDUCIBILITY_ABBREV)
      (let [node (ctor! world value 2 0 4)
            height (scalar/read-bytes (:layout node) (:scalar-bytes node)
                     {:index 0 :offset 0 :type "uint32" :region :scalar})]
        ;; Lean's UInt32 regular height includes zero and does not alias abbrev.
        (leaf (long height))))
    :axiom-val
    (let [node (ctor! world value 0 1 1) [constant] (:fields node)]
      (when-not (= 0 (byte-at node 0))
        (fail "Only safe axioms are supported" {}))
      {:children [[:constant-val constant]]
       :build (fn [[{:keys [name params type]}]]
                (ConstantInfo/mkAxiom name (object-array params) type false))})
    :axiom-declaration
    (let [[axiom] (:fields (ctor! world value 0 1 0))]
      {:children [[:axiom-val axiom]] :build first})
    :compiler-marker-constant
    (let [[name params type] (:fields (ctor! world value 0 3 0))
          [parent text] (:fields (ctor! world name 1 2 8))
          [level] (:fields (ctor! world type 3 1 8))
          [zero] (:fields (ctor! world level 1 1 8))
          text (string/string-value carrier-ops world text)]
      ;; Test the raw guest shape before projection: mdata and normalized
      ;; max/imax universes must not widen this three-declaration capability.
      (when-not (and (= 0 (scalar-tag parent))
                     (string? text) (contains? #{"lcAny" "lcErased" "lcVoid"} text)
                     (= 0 (scalar-tag params)) (= 0 (scalar-tag zero)))
        (fail "Expected an exact pinned compiler marker" {}))
      {:children [[:name name] [:expr type]]
       :build (fn [[name type]] (ConstantInfo/mkAxiom name (object-array []) type true))})
    :compiler-marker-val
    (let [node (ctor! world value 0 1 1) [constant] (:fields node)]
      (when-not (= 1 (byte-at node 0))
        (fail "Compiler marker must preserve isUnsafe=true" {}))
      {:children [[:compiler-marker-constant constant]] :build first})
    :compiler-marker-declaration
    (let [[axiom] (:fields (ctor! world value 0 1 0))]
      {:children [[:compiler-marker-val axiom]] :build first})
    :definition-val
    (let [node (ctor! world value 0 4 1) [constant value hints all] (:fields node)]
      ;; Safe single definitions only; unsafe/partial recursion needs group admission.
      (when-not (= 1 (byte-at node 0)) (fail "Only safe single definitions are supported" {}))
      {:children [[:constant-val constant] [:expr value] [:hints hints] [:names all]]
       :build (fn [[{:keys [name params type]} body hints all]]
                (when-not (= [name] (vec all)) (fail "Expected one-member definition metadata" {}))
                (ConstantInfo/mkDefWithHints name (object-array params) type body (long hints) (byte 0) (object-array all)))})
    :declaration
    (let [[definition] (:fields (ctor! world value 1 1 0))]
      {:children [[:definition-val definition]] :build first})
    (fail "Unsupported kernel projection kind" {:kind kind})))

(defn make-projector
  "Capture exactly WORLD and one private typed memo for a bulk projection scope.
   The returned function accepts [world kind value] and rejects even an equal
   independent world. No global cache or guest state/ownership changes occur.
   Keep this context invocation-local; dropping it releases intermediate memo
   entries while its returned Java values retain their ordinary immutable DAG."
  [world]
  (let [^HashMap memo (HashMap.)]
    (fn [current-world kind value]
      (when-not (identical? world current-world)
        (fail "Kernel projector belongs to a different world" {}))
      (locking memo
        (let [root [kind value]]
          (loop [work [[:visit root]] active #{}]
            (if (empty? work) {:value (.get memo root) :projected-nodes (.size memo)}
              (let [[op key spec] (peek work) work (pop work)]
                (case op
                  :visit (if (.containsKey memo key) (recur work active)
                           (do (when (contains? active key) (fail "Cyclic guest kernel value" {:kind (first key)}))
                               (let [spec (specification world (first key) (second key))]
                                 (recur (into (conj work [:build key spec])
                                              (map #(vector :visit %) (reverse (:children spec))))
                                        (conj active key)))))
                  :build (do (.put memo key ((:build spec) (mapv #(.get memo %) (:children spec))))
                             (recur work (disj active key))))))))))))

(defn project-with-stats
  "Project with a fresh memo by default, or an explicit same-world context.
   :projected-nodes is cumulative within the supplied context."
  ([world kind value] ((make-projector world) world kind value))
  ([world kind value projector] (projector world kind value)))

(defn project-name
  ([world value] (:value (project-with-stats world :name value)))
  ([world value projector] (:value (project-with-stats world :name value projector))))
(defn project-name-bounded
  "Borrow a validated Name with explicit spine-node and UTF-16 string limits.
   Counts the anonymous terminator as a node. Reject cycles before projection;
   does not inspect a constant's type/body or establish any admission authority."
  [world value {:keys [max-nodes max-chars] :as limits}]
  (when-not (and (map? limits) (= #{:max-nodes :max-chars} (set (keys limits)))
                 (every? #(and (integer? %) (<= 1 % Long/MAX_VALUE)) [max-nodes max-chars]))
    (fail "Bounded Name projection requires positive node and character limits" {}))
  (loop [current value seen #{} remaining max-nodes characters 0]
    (when (zero? remaining) (fail "Guest Name exceeds spine-node limit" {:limit max-nodes}))
    (if (= 0 (scalar-tag current))
      (project-name world value)
      (do
        (when (contains? seen current) (fail "Cyclic guest Name" {}))
        (let [tag (:tag (m/node world current))
              node (ctor! world current tag 2 8)
              [parent payload] (:fields node)
              length (case tag
                       1 (count (string/string-value carrier-ops world payload))
                       2 (do (long! world payload) 0)
                       (fail "Invalid guest Name tag" {:tag tag}))
              characters (+ characters length)]
          (when (> characters max-chars)
            (fail "Guest Name exceeds string-character limit" {:limit max-chars}))
          (recur parent (conj seen current) (dec remaining) characters))))))

(defn project-level
  ([world value] (:value (project-with-stats world :level value)))
  ([world value projector] (:value (project-with-stats world :level value projector))))
(defn project-expr
  ([world value] (project-expr world value (make-projector world)))
  ([world value projector]
   (let [^Expr result (:value (project-with-stats world :expr value projector))]
     (when (pos? (.bvarRange result)) (fail "Loose bound variable in closed guest expression" {}))
     result)))

(defn admit-definition
  "Strict safe defnDecl admission. Returns a NEW Java Env and original guest root.
   Does not update a Lean guest Environment or install executable code."
  ([world env declaration] (admit-definition world env declaration 1000000))
  ([world ^Env env declaration fuel]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE)) (fail "Invalid checking fuel" {:fuel fuel}))
   (let [^ConstantInfo constant (:value (project-with-stats world :declaration declaration))
         next-env (TypeChecker/checkConstant env constant (long fuel))]
     {:env next-env :constant constant :world world :guest-declaration declaration})))

(defn admit-axiom
  "Check an explicitly requested safe axiom against a Java Env. This validates
   its type but introduces an assumption; callers must apply their axiom policy.
   Returns a new Env and preserves the original guest declaration unchanged."
  ([world env declaration] (admit-axiom world env declaration 1000000))
  ([world ^Env env declaration fuel]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE))
     (fail "Invalid checking fuel" {:fuel fuel}))
   (let [^ConstantInfo constant (:value (project-with-stats world :axiom-declaration declaration))
         next-env (TypeChecker/checkConstant env constant (long fuel))]
     {:env next-env :constant constant :world world :guest-declaration declaration})))


(defn compiler-marker-declaration?
  "Recognize the exact pinned three-marker shape; this does not admit it.
   Malformed or broader unsafe declarations are not marker capabilities."
  [world declaration]
  (try (project-with-stats world :compiler-marker-declaration declaration) true
       (catch clojure.lang.ExceptionInfo _ false)))

(defn admit-compiler-marker
  "Strict bootstrap-only admission of lcAny/lcErased/lcVoid: anonymous str name,
   no universe parameters, exact raw Sort(succ zero), isUnsafe=true.
   Does not enable arbitrary unsafe axiom checking or unchecked publication."
  ([world env declaration] (admit-compiler-marker world env declaration 1000000))
  ([world ^Env env declaration fuel]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE))
     (fail "Invalid checking fuel" {:fuel fuel}))
   (let [^ConstantInfo constant (:value (project-with-stats world :compiler-marker-declaration declaration))
         next-env (TypeChecker/checkConstant env constant (long fuel))]
     {:env next-env :constant constant :world world :guest-declaration declaration})))
