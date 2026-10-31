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
(def ^:private default-carrier-ops {:ref? m/ref? :node m/node})
(defn- nat! [ops world value] (native/nat-value ops world value))
(defn- long! [ops world value]
  (let [n (nat! ops world value)]
    (when (> n Long/MAX_VALUE) (fail "Guest Nat exceeds Java long representation" {:value value})) (long n)))
(defn- scalar-tag [ops v]
  (cond (native/native-scalar? v) (native/payload v)
        (integer? v) (long! ops nil v) (instance? prototype.machine.Tag v) (:tag v) :else nil))

(defn constructor-layout?
  "Pinned semantic storage, or validated native/imported raw clone padding.
   Storage witnesses never establish native object or kernel identity."
  [node fields scalar-size]
  (constructor/constructor-layout? node fields scalar-size))
(defn- ctor! [ops world value tag fields scalar-size]
  (when-not ((:ref? ops) value) (fail "Expected guest constructor reference" {:value value}))
  (let [node ((:node ops) world value)
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

(defn- specification [ops world kind value]
  (case kind
    :nat (leaf (nat! ops world value))
    :string (leaf (string/string-value ops world value))
    :name
    (if (= 0 (scalar-tag ops value)) (leaf Name/ANONYMOUS_NAME)
      (let [tag (:tag ((:node ops) world value)) node (ctor! ops world value tag 2 8) [parent payload] (:fields node)]
        (case tag
          1 {:children [[:name parent] [:string payload]] :build (fn [[p s]] (Name/mkStr p s))}
          2 {:children [[:name parent]] :build (fn [[p]] (Name/mkNum p (long! ops world payload)))}
          (fail "Invalid guest Name tag" {:tag tag}))))
    :level
    (if (= 0 (scalar-tag ops value)) (leaf Level/ZERO_LEVEL)
      (let [tag (:tag ((:node ops) world value))
            _ (when (= 5 tag) (fail "Unresolved guest level metavariable" {}))
            count (case tag 1 1 (2 3) 2 4 1 (fail "Invalid guest Level tag" {:tag tag}))
            node (ctor! ops world value tag count 8) [a b] (:fields node)]
        (case tag
          1 {:children [[:level a]] :build (fn [[a]] (Level/succ a))}
          2 {:children [[:level a] [:level b]] :build (fn [[a b]] (Level/max a b))}
          3 {:children [[:level a] [:level b]] :build (fn [[a b]] (Level/imax a b))}
          4 {:children [[:name a]] :build (fn [[a]] (Level/param a))})))
    (:names :levels)
    (if (= 0 (scalar-tag ops value)) (leaf '())
      (let [[head tail] (:fields (ctor! ops world value 1 2 0))]
        {:children [[(if (= kind :names) :name :level) head] [kind tail]] :build (fn [[head tail]] (cons head tail))}))
    :literal
    (let [tag (:tag ((:node ops) world value)) [payload] (:fields (ctor! ops world value tag 1 0))]
      (case tag
        0 {:children [[:nat payload]] :build (fn [[n]] (Expr/litNat n))}
        1 {:children [[:string payload]] :build (fn [[s]] (Expr/litStr s))}
        (fail "Invalid guest Literal tag" {:tag tag})))
    :expr
    (let [tag (:tag ((:node ops) world value))
          _ (when (contains? #{1 2} tag) (fail "Unresolved guest free/metavariable" {:tag tag}))
          [fields size] (case tag (0 3 9) [1 8] (4 5 10) [2 8] (6 7) [3 9] 8 [4 9] 11 [3 8]
                         (fail "Invalid guest Expr tag" {:tag tag}))
          node (ctor! ops world value tag fields size) [a b c d] (:fields node)]
      (case tag
        0 (let [idx (long! ops world a)]
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
        11 {:children [[:name a] [:expr c]] :build (fn [[n e]] (Expr/proj n (long! ops world b) e))}))
    :constant-val
    (let [[name params type] (:fields (ctor! ops world value 0 3 0))]
      {:children [[:name name] [:names params] [:expr type]]
       :build (fn [[n p t]] {:name n :params p :type t})})
    :hints
    (case (scalar-tag ops value)
      0 (leaf ConstantInfo/REDUCIBILITY_OPAQUE)
      1 (leaf ConstantInfo/REDUCIBILITY_ABBREV)
      (let [node (ctor! ops world value 2 0 4)
            height (scalar/read-bytes (:layout node) (:scalar-bytes node)
                     {:index 0 :offset 0 :type "uint32" :region :scalar})]
        ;; Lean's UInt32 regular height includes zero and does not alias abbrev.
        (leaf (long height))))
    :axiom-val
    (let [node (ctor! ops world value 0 1 1) [constant] (:fields node)]
      (when-not (= 0 (byte-at node 0))
        (fail "Only safe axioms are supported" {}))
      {:children [[:constant-val constant]]
       :build (fn [[{:keys [name params type]}]]
                (ConstantInfo/mkAxiom name (object-array params) type false))})
    :axiom-declaration
    (let [[axiom] (:fields (ctor! ops world value 0 1 0))]
      {:children [[:axiom-val axiom]] :build first})
    :theorem-val
    ;; Lean 819816b2 Declaration.lean:142-153: ConstantVal, value, all;
    ;; no safety scalar and no singleton restriction on mutual-block metadata.
    (let [[constant proof all] (:fields (ctor! ops world value 0 3 0))]
      {:children [[:constant-val constant] [:expr proof] [:names all]]
       :build (fn [[{:keys [name params type]} proof all]]
                (ConstantInfo/mkThm name (object-array params) type proof (object-array all)))})
    :theorem-declaration
    (let [[theorem] (:fields (ctor! ops world value 2 1 0))]
      {:children [[:theorem-val theorem]] :build first})
    :compiler-marker-constant
    (let [[name params type] (:fields (ctor! ops world value 0 3 0))
          [parent text] (:fields (ctor! ops world name 1 2 8))
          [level] (:fields (ctor! ops world type 3 1 8))
          [zero] (:fields (ctor! ops world level 1 1 8))
          text (string/string-value ops world text)]
      ;; Test the raw guest shape before projection: mdata and normalized
      ;; max/imax universes must not widen this three-declaration capability.
      (when-not (and (= 0 (scalar-tag ops parent))
                     (string? text) (contains? #{"lcAny" "lcErased" "lcVoid"} text)
                     (= 0 (scalar-tag ops params)) (= 0 (scalar-tag ops zero)))
        (fail "Expected an exact pinned compiler marker" {}))
      {:children [[:name name] [:expr type]]
       :build (fn [[name type]] (ConstantInfo/mkAxiom name (object-array []) type true))})
    :compiler-marker-val
    (let [node (ctor! ops world value 0 1 1) [constant] (:fields node)]
      (when-not (= 1 (byte-at node 0))
        (fail "Compiler marker must preserve isUnsafe=true" {}))
      {:children [[:compiler-marker-constant constant]] :build first})
    :compiler-marker-declaration
    (let [[axiom] (:fields (ctor! ops world value 0 1 0))]
      {:children [[:compiler-marker-val axiom]] :build first})
    :definition-val
    (let [node (ctor! ops world value 0 4 1) [constant value hints all] (:fields node)]
      ;; Safe single definitions only; unsafe/partial recursion needs group admission.
      (when-not (= 1 (byte-at node 0)) (fail "Only safe single definitions are supported" {}))
      {:children [[:constant-val constant] [:expr value] [:hints hints] [:names all]]
       :build (fn [[{:keys [name params type]} body hints all]]
                (when-not (= [name] (vec all)) (fail "Expected one-member definition metadata" {}))
                (ConstantInfo/mkDefWithHints name (object-array params) type body (long hints) (byte 0) (object-array all)))})
    :declaration
    (let [[definition] (:fields (ctor! ops world value 1 1 0))]
      {:children [[:definition-val definition]] :build first})
    :definition-val-general
    (let [node (ctor! ops world value 0 4 1) [constant body hints all] (:fields node)
          safety (case (byte-at node 0) 0 1 1 0 2 2 (fail "Invalid original DefinitionSafety" {}))]
      {:children [[:constant-val constant] [:expr body] [:hints hints] [:names all]]
       :build (fn [[{:keys [name params type]} body hints all]]
                (ConstantInfo/mkDefWithHints name (object-array params) type body (long hints) (byte safety) (object-array all)))})
    :definition-values
    (if (= 0 (scalar-tag ops value)) (leaf '())
      (let [[head tail] (:fields (ctor! ops world value 1 2 0))]
        {:children [[:definition-val-general head] [:definition-values tail]] :build (fn [[head tail]] (cons head tail))}))
    :mutual-declaration
    (let [[values] (:fields (ctor! ops world value 5 1 0))]
      {:children [[:definition-values values]] :build (fn [[values]] (vec values))})
    (fail "Unsupported kernel projection kind" {:kind kind})))

(defn ^:no-doc default-world-specification-reader
  "Internal shared semantic decomposition contract for alternate m.World walkers.
   Capture WORLD and return [kind value] -> {:children [[kind value] ...], :build f}.
   One call performs the existing bounded node/layout decomposition, not a graph
   traversal, memoization or admission. The consumer must enforce world identity,
   scope lifetime, cycle detection and traversal/resource bounds. This reader
   intentionally uses the default carrier; custom carriers use make-projector."
  [world]
  (fn [kind value] (specification default-carrier-ops world kind value)))

(defn make-projector
  "Capture exactly WORLD and one private typed memo for a projection scope.
   Optional carrier ops have :ref? [value], :node [world value] and optional
   :check! []. They supply storage views, never semantic projection rules.
   check! runs even on memo hits and every traversal iteration. The returned
   function has a :prototype.kernel-bridge/clear-memo! metadata hook which clears
   the memo under the same lock; carrier lifetime/invalidating ops remain the
   adapter's responsibility. Default arity preserves m.World behavior."
  ([world] (make-projector world default-carrier-ops))
  ([world ops]
   (when-not (and (map? ops) (fn? (:ref? ops)) (fn? (:node ops))
                  (every? #{:ref? :node :check!} (keys ops))
                  (or (nil? (:check! ops)) (fn? (:check! ops))))
     (fail "Invalid checking projection carrier operations" {}))
   (let [^HashMap memo (HashMap.) check! (or (:check! ops) (fn [] nil))]
     (with-meta
       (fn [current-world kind value]
         (when-not (identical? world current-world)
           (fail "Kernel projector belongs to a different world" {}))
         (locking memo
           (check!)
           (let [root [kind value]]
             (loop [work [[:visit root]] active #{}]
               (check!)
               (if (empty? work) {:value (.get memo root) :projected-nodes (.size memo)}
                 (let [[op key spec] (peek work) work (pop work)]
                   (case op
                     :visit (if (.containsKey memo key) (recur work active)
                              (do (when (contains? active key) (fail "Cyclic guest kernel value" {:kind (first key)}))
                                  (let [spec (specification ops world (first key) (second key))]
                                    (recur (into (conj work [:build key spec])
                                                 (map #(vector :visit %) (reverse (:children spec))))
                                           (conj active key)))))
                     :build (do (.put memo key ((:build spec) (mapv #(.get memo %) (:children spec))))
                                (recur work (disj active key))))))))))
       {::clear-memo! (fn [] (locking memo (.clear memo)))
        ::memo-size (fn [] (locking memo (.size memo)))}))))

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
  ([world value limits] (project-name-bounded world value limits default-carrier-ops))
  ([world value {:keys [max-nodes max-chars] :as limits} ops]
  (when-not (and (map? limits) (= #{:max-nodes :max-chars} (set (keys limits)))
                 (every? #(and (integer? %) (<= 1 % Long/MAX_VALUE)) [max-nodes max-chars]))
    (fail "Bounded Name projection requires positive node and character limits" {}))
  (loop [current value seen #{} remaining max-nodes characters 0]
    (when (zero? remaining) (fail "Guest Name exceeds spine-node limit" {:limit max-nodes}))
    (if (= 0 (scalar-tag ops current))
      (project-name world value (make-projector world ops))
      (do
        (when (contains? seen current) (fail "Cyclic guest Name" {}))
        (let [tag (:tag ((:node ops) world current))
              node (ctor! ops world current tag 2 8)
              [parent payload] (:fields node)
              length (case tag
                       1 (count (string/string-value ops world payload))
                       2 (do (long! ops world payload) 0)
                       (fail "Invalid guest Name tag" {:tag tag}))
              characters (+ characters length)]
          (when (> characters max-chars)
            (fail "Guest Name exceeds string-character limit" {:limit max-chars}))
          (recur parent (conj seen current) (dec remaining) characters)))))))

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
  ([world env declaration fuel] (admit-definition world env declaration fuel (make-projector world)))
  ([world ^Env env declaration fuel projector]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE)) (fail "Invalid checking fuel" {:fuel fuel}))
   (let [^ConstantInfo constant (:value (project-with-stats world :declaration declaration projector))
         next-env (TypeChecker/checkConstant env constant (long fuel))]
     {:env next-env :constant constant :world world :guest-declaration declaration})))

(defn admit-axiom
  "Check an explicitly requested safe axiom against a Java Env. This validates
   its type but introduces an assumption; callers must apply their axiom policy.
   Returns a new Env and preserves the original guest declaration unchanged."
  ([world env declaration] (admit-axiom world env declaration 1000000))
  ([world env declaration fuel] (admit-axiom world env declaration fuel (make-projector world)))
  ([world ^Env env declaration fuel projector]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE))
     (fail "Invalid checking fuel" {:fuel fuel}))
   (let [^ConstantInfo constant (:value (project-with-stats world :axiom-declaration declaration projector))
         next-env (TypeChecker/checkConstant env constant (long fuel))]
     {:env next-env :constant constant :world world :guest-declaration declaration})))

(defn admit-theorem
  "Strict thmDecl admission: check the proposition and its proof before adding
   the theorem to a NEW Java Env. Preserves the complete all-name metadata and
   original guest root; does not publish into a guest Environment. An explicit
   projector supplies the same carrier/lifetime/resource policy as other admissions."
  ([world env declaration] (admit-theorem world env declaration 1000000))
  ([world env declaration fuel] (admit-theorem world env declaration fuel (make-projector world)))
  ([world ^Env env declaration fuel projector]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE))
     (fail "Invalid checking fuel" {:fuel fuel}))
   (let [^ConstantInfo constant (:value (project-with-stats world :theorem-declaration declaration projector))
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


(defn admit-mutual-definitions
  "Strict original unsafe/partial group check, not a frontend policy grant.
   Caller must separately authorize generated admission. Every header is checked
   in the old Env; all bodies are checked only after the whole group is present."
  [world ^Env env declaration fuel projector]
  (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE)) (fail "Invalid checking fuel" {}))
  (let [constants (:value (project-with-stats world :mutual-declaration declaration projector))
        names (mapv #(.name ^ConstantInfo %) constants)]
    (when-not (and (<= 1 (count constants) 256) (= (count names) (count (set names))))
      (fail "Invalid bounded unique mutual definition group" {}))
    {:env (TypeChecker/checkMutualDefinitions env constants (long fuel)) :constants constants
     :world world :guest-declaration declaration}))
