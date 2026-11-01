(ns prototype.native-nat
  "Internal bounded Nat arithmetic with source-owned registry guards. Plans
   own no guest state or registry values. Declines require ordinary execution."
  (:require [prototype.runtime-prim]
            [prototype.native-scalar]
            [prototype.machine]
            [prototype.mutable])
  (:import [java.lang.ref WeakReference]))

(def ^:private owner (Object.))
(defonce ^:private declined (Object.))
(defn decline? [result] (identical? declined result))

(def ^:private operations
  {"lean_nat_add" :add "lean_nat_sub" :nat-sub "lean_nat_dec_eq" :eq
   "lean_nat_dec_lt" :lt "lean_nat_mod" :mod})

;; Resolve aliases at the runtime definition owner.
(def ^:private earlier-routes
  '[unsigned-casts ffi-build-queries numeric-build-queries pinned-build
    string/supported-symbols object/supported-symbols float/supported-symbols
    thunk/supported-symbols thunk/internal-symbols
    task/supported-symbols task/internal-symbols expr/supported-symbols
    sharecommon/supported-symbols expr-replace/internal-symbols
    search/internal-symbols transform/supported-symbols bvars/supported-symbols
    mvars/supported-symbols mvars/internal-symbols
    expr-mvars/supported-symbols expr-mvars/internal-symbols
    io/supported-symbols sync/supported-symbols heartbeat/supported-symbols])

(defn- runtime-var [symbol] (ns-resolve 'prototype.runtime-prim symbol))
(defn- ordinary-map? [table]
  (or (= clojure.lang.PersistentArrayMap (class table))
      (= clojure.lang.PersistentHashMap (class table))))
(defn- absent? [table symbol]
  (and (or (ordinary-map? table) (= clojure.lang.PersistentHashSet (class table)))
       (not (contains? table symbol))))

(defn- owner-roots?
  "Definition-owner vectors reject preparation under semantic redefinitions."
  [namespace roots-name names]
  (let [roots @(ns-resolve namespace roots-name)]
    (and (vector? roots) (= (count roots) (count names))
         (every? true? (map (fn [expected name]
                             (identical? expected @(ns-resolve namespace name))) roots names)))))

(defn- stock-owners? []
  (and
   (owner-roots? 'prototype.runtime-prim 'nat-arithmetic-roots
                 '[evaluate numeric nat! exact! add negate fail])
   (owner-roots? 'prototype.native-scalar 'native-number-roots
                 '[number-value nat-value payload])
   (identical? @(ns-resolve 'prototype.native-scalar 'scalar-carrier-root)
               @(ns-resolve 'prototype.native-scalar 'native-scalar?))
   (@(ns-resolve 'prototype.native-scalar 'builtin-native-number?))
   (owner-roots? 'prototype.machine 'scalar-reference-roots '[ref? node native-reference?])
   (@(ns-resolve 'prototype.machine 'builtin-scalar-reference?))
   ;; The parent uses runtime-value! as its fallback. Do not teach a descriptor
   ;; a custom entry point or injected ops map while preparing under redefs.
   (let [roots @(ns-resolve 'prototype.mutable 'scalar-wrapper-roots)]
     (and (identical? (nth roots 0) @(ns-resolve 'prototype.mutable 'runtime-value!))
          (identical? (nth roots 1) @(ns-resolve 'prototype.mutable 'runtime-ops))))))

(defn- route? [symbol operation]
  (let [supported @(runtime-var 'supported-symbols)
        scalar @(runtime-var 'scalar-operations)
        signed @(runtime-var 'fixed-signed-operations)]
    (and (ordinary-map? supported) (ordinary-map? (get supported symbol))
         (= {:arity 2} (get supported symbol))
         (ordinary-map? scalar) (ordinary-map? signed)
         (= operation (get scalar symbol)) (not (contains? signed symbol))
         (every? #(absent? @(runtime-var %) symbol) earlier-routes)
         ;; Redundant with the independent proof above, deliberately retained
         ;; to exercise the owner's exact current classification too.
         (@(runtime-var 'builtin-numeric-route?) symbol operation))))

(defn- qualified-vars [namespace names]
  (mapv #(ns-resolve namespace %) names))

(defn- watched-vars []
  (vec
   (concat
    (map runtime-var (concat '[supported-symbols scalar-operations fixed-signed-operations
                              nat-arithmetic-roots nat-arithmetic-generation nat-arithmetic-token
                              builtin-nat-arithmetic? builtin-numeric-route?
                              ordinary-scalar-table? scalar-route-absent?
                              evaluate numeric nat! exact! add negate fail]
                            earlier-routes))
    (qualified-vars 'prototype.native-scalar
                    '[native-number-roots native-number-generation native-number-token
                      builtin-native-number? number-value nat-value payload
                      scalar-carrier-root scalar-carrier-generation scalar-carrier-token
                      builtin-scalar-carrier? native-scalar?])
    (qualified-vars 'prototype.machine
                    '[scalar-reference-roots scalar-reference-generation scalar-reference-token
                      builtin-scalar-reference? ref? node native-reference?])
    (qualified-vars 'prototype.mutable
                    '[scalar-wrapper-roots scalar-wrapper-generation scalar-wrapper-token
                      runtime-value! runtime-ops]))))

(defn- watch [v]
  ;; Even registry values are weak: replacing a registry must not retain old
  ;; executable owners, opaque literals, or data through prepared host code.
  [(WeakReference. v) (WeakReference. @v)])

(defn- current? [watches]
  (loop [i 0]
    (if (= i (count watches)) true
      (let [[^WeakReference variable ^WeakReference expected] (nth watches i)
            v (.get variable) value (.get expected)]
        (and v value (identical? value @v) (recur (inc i)))))))

(defn prepare-op
  "Return a guarded descriptor for one exact binary Nat extern, else nil.
   Registry membership, signature and route are proven only at preparation;
   each invocation checks weak identities. No custom evaluate root is learned."
  [symbol]
  (when-let [operation (get operations symbol)]
    (when (and (stock-owners?) (route? symbol operation))
      (let [variables (watched-vars)
            watches (mapv watch variables)]
        ;; Fail closed if something changed while assembling the descriptor.
        (when (and (current? watches) (stock-owners?) (route? symbol operation))
          {:owner owner :symbol symbol :operation operation :watches watches})))))

(defn try-op
  "Return the legacy Long result, or an opaque decline token. Addition overflow
   declines so the ordinary runtime retains its BigInt promotion and carrier.
   Raw natives, refs, negative Longs and all other carriers also decline."
  [descriptor a b]
  (if-not (and (identical? owner (:owner descriptor))
               (= Long (class a)) (= Long (class b))
               (<= 0 (long a)) (<= 0 (long b))
               (current? (:watches descriptor)))
    declined
    (let [a (long a) b (long b)]
      (case (:operation descriptor)
        :add (if (<= a (unchecked-subtract Long/MAX_VALUE b)) (unchecked-add a b) declined)
        :nat-sub (if (< a b) (long 0) (unchecked-subtract a b))
        :eq (if (== a b) (long 1) (long 0))
        :lt (if (< a b) (long 1) (long 0))
        :mod (if (zero? b) a (rem a b))
        declined))))
