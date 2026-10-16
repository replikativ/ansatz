(ns prototype.import-ir
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.machine :as m]))

(defn name-label [[op parent part]]
  (case op "anonymous" "" (let [p (name-label parent)] (str p (when (seq p) ".") part))))

(defn operand [a]
  (cond (= a "erased") [:imm m/erased]
        (:var a) [:var (get-in a [:var :id :idx])]
        :else (m/fail "Unknown imported operand" {:operand a})))

(defn layout! [i]
  (when-not (and (zero? (:usize i)) (zero? (:ssize i)))
    (m/fail "Scalar constructor layout not implemented" {:layout i})))

(defn type! [ty]
  (when-not (contains? #{"erased" "object" "tobject" "tagged" "uint8"} ty)
    (m/fail "Unsupported imported runtime type" {:type ty})))

(defn expression [e]
  (let [[op data] (first e)]
    (case op
      :ctor (do (layout! (:i data))
                (when-not (= (count (:ys data)) (get-in data [:i :size]))
                  (m/fail "Constructor field count mismatch" {:constructor data}))
                [:ctor (get-in data [:i :cidx]) (mapv operand (:ys data))])
      :proj [:project [:var (get-in data [:x :idx])] (:i data)]
      :isShared [:shared? [:var (get-in data [:x :idx])]]
      :fap [:invoke [:direct (:c data)] (mapv operand (:ys data))]
      :pap [:closure (:c data) (mapv operand (:ys data))]
      :ap [:invoke [:closure [:var (get-in data [:x :idx])]] (mapv operand (:ys data))]
      :lit [:literal (or (get-in data [:v :num :v]) (get-in data [:v :str :v]))]
      (m/fail "Unsupported imported expression" {:expression e}))))

(declare body)
(defn alternative [[op a b]]
  (case op "ctor" [(:cidx a) (body b)] "default" [:default (body a)]
        (m/fail "Unknown alternative" {:op op})))

(defn body [[op a b c d e]]
  (case op
    "vdecl" (let [_ (type! b) x (:idx a) expr (expression c) continuation (body d)]
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
    (m/fail "Unsupported imported instruction" {:op op})))

(defn load-bundle [path]
  (let [rows (mapv #(json/read-str % :key-fn keyword :bigdec false) (str/split-lines (slurp path)))
        manifest (first rows)]
    (when-not (and (= "lean-ir-probe/1" (:schema manifest)) (= "4.33.1" (:leanVersion manifest)))
      (m/fail "Unsupported producer" {:manifest manifest}))
    (into {} (for [row (rest rows)]
               (let [f (get-in row [:ir :fdecl])]
                 (when-not f (m/fail "Missing body or extern" {:name (:name row)}))
                 (type! (:type f))
                 (doseq [p (:xs f)] (type! (:ty p)))
                 [(:f f) {:params (mapv #(get-in % [:x :idx]) (:xs f)) :body (body (:body f))}])))))
