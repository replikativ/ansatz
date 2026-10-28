(ns bulk-sparse-joins
  "Research-only join storage. Load in an existing REPL; no production hooks.
   run-with-runtime thunks must return frozen Worlds, never private Machines."
  (:require [prototype.mutable :as u]
            [prototype.machine :as m])
  (:import [java.util AbstractMap$SimpleImmutableEntry HashMap Arrays]))

;; The carrier and marker survive reloading this research namespace. Arrays are
;; owned by the holder and never mutated after construction or exposed in Worlds.
(defonce ^:private marker (Object.))
(def ^:private mutable-ctl-var (ns-resolve 'prototype.mutable 'ctl))
(def ^:private mutable-unbound-var (ns-resolve 'prototype.mutable 'unbound))

(defn sparse? [x]
  (and (instance? AbstractMap$SimpleImmutableEntry x)
       (identical? marker (.getKey ^AbstractMap$SimpleImmutableEntry x))))

(defn capture
  "Capture all bound slots after lexical overrides. IDs must be sorted, unique,
   in range; both override vectors must have equal lengths. Inputs are borrowed
   only for this call. Logical RC is unaffected."
  [^objects base override-ids override-values unbound]
  (let [width (alength base)
        overrides (count override-ids)]
    (when-not (= overrides (count override-values))
      (throw (ex-info "Sparse override arity" {})))
    (dotimes [j overrides]
      (let [id (nth override-ids j)]
        (when-not (and (integer? id) (<= 0 id) (< id width)
                       (or (zero? j) (< (nth override-ids (dec j)) id)))
          (throw (ex-info "Invalid sparse override ID" {:id id})))))
    (let [size (loop [i 0 j 0 n 0]
                 (if (= i width) n
                   (let [override? (and (< j overrides) (= i (nth override-ids j)))
                         value (if override? (nth override-values j) (aget base i))]
                     (recur (inc i) (if override? (inc j) j)
                            (if (identical? unbound value) n (inc n))))))
          ids (int-array (inc size))
          values (object-array size)]
      (aset-int ids 0 width)
      (loop [i 0 j 0 n 0]
        (when (< i width)
          (let [override? (and (< j overrides) (= i (nth override-ids j)))
                value (if override? (nth override-values j) (aget base i))
                bound? (not (identical? unbound value))]
            (when bound?
              (aset-int ids (inc n) i)
              (aset values n value))
            (recur (inc i) (if override? (inc j) j) (if bound? (inc n) n)))))
      (let [storage (object-array 2)]
        (aset storage 0 ids)
        (aset storage 1 values)
        (AbstractMap$SimpleImmutableEntry. marker storage)))))

(defn bindings
  "Export precisely the ordinary locals map, without a full-width array."
  [^AbstractMap$SimpleImmutableEntry holder unbound]
  (let [^objects storage (.getValue holder)
        ^ints ids (aget storage 0)
        ^objects values (aget storage 1)]
    (persistent!
     (loop [i 0 result (transient {})]
       (if (= i (alength values)) result
         (let [value (aget values i)]
           (recur (inc i) (if (identical? unbound value) result
                           (assoc! result (long (aget ids (inc i))) value)))))))))

(defn restore
  "Restore a fresh full-width register array. The holder remains reusable."
  [^AbstractMap$SimpleImmutableEntry holder unbound]
  (let [^objects storage (.getValue holder)
        ^ints ids (aget storage 0)
        ^objects values (aget storage 1)
        result (object-array (aget ids 0))]
    (Arrays/fill ^objects result unbound)
    (dotimes [i (alength values)] (aset result (aget ids (inc i)) (aget values i)))
    result))

(defn capture!
  "Compiler probe entry: install an owned sparse capture in current joins."
  [machine id params body base override-ids override-values]
  (let [ctl @mutable-ctl-var
        unbound @mutable-unbound-var]
    (.put ^HashMap (ctl machine 2) id
          (object-array [params body (capture base override-ids override-values unbound)]))))

(defn run-with-runtime
  "Temporarily support sparse joins in freeze/jump, conservatively declining
   unchanged-host storage reuse. Thunk must freeze every Machine before return;
   do not run concurrent runtime users while these research redefinitions hold."
  [thunk]
  (let [resolve-var #(ns-resolve 'prototype.mutable %)
        joins-var (resolve-var 'joins-out)
        jump-var (resolve-var 'jump-values!)
        boundary-var (resolve-var 'boundary-arrays-fit?)
        dense-bindings @(resolve-var 'bindings)
        dense-jump @jump-var
        ctl @(resolve-var 'ctl)
        put! @(resolve-var 'put!)
        bind-params! @(resolve-var 'bind-params!)
        unbound @(resolve-var 'unbound)
        joins-out (fn [joins]
                    (into {} (map (fn [[id join]]
                                    (let [^objects join join locals (aget join 2)]
                                      [id {:params (aget join 0) :body (aget join 1)
                                           :locals (if (sparse? locals)
                                                     (bindings locals unbound)
                                                     (dense-bindings locals))}])) joins)))
        jump (fn [machine id args]
               (let [^objects join (.get ^HashMap (ctl machine 2) id)]
                 (if (and join (sparse? (aget join 2)))
                   (do
                     (when-not (= (count (aget join 0)) (count args))
                       (m/fail "Invalid join" {:join id}))
                     (let [locals (restore (aget join 2) unbound)]
                       (bind-params! locals (aget join 0) args)
                       (put! machine 1 locals)
                       (put! machine 0 (aget join 1))))
                   (dense-jump machine id args))))]
    (with-redefs-fn {joins-var joins-out jump-var jump boundary-var (fn [_ _] false)} thunk)))

(defn check-pure!
  "Cheap REPL checks for nil/dead bindings, override precedence, input ownership,
   original width and repeated restoration. Returns true or throws."
  []
  (let [unbound (Object.)
        base (object-array [unbound nil :dead :old unbound])
        captured (capture base [0 3 4] [:new unbound :last] unbound)
        expected {0 :new 1 nil 2 :dead 4 :last}
        first-copy (restore captured unbound)]
    (assert (sparse? captured))
    (assert (= expected (bindings captured unbound)))
    (assert (= 5 (alength ^objects first-copy)))
    (assert (identical? unbound (aget ^objects first-copy 3)))
    (aset base 2 :changed-input)
    (aset first-copy 2 :changed-output)
    (assert (= expected (bindings captured unbound)))
    (assert (= :dead (aget ^objects (restore captured unbound) 2)))
    (assert (= {} (bindings (capture (object-array 0) [] [] unbound) unbound)))
    true))
