(ns prototype.source-graph-plan-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.source-graph-plan :as graph]))

(def limits {:max-modules 32 :max-roots 16 :max-edges 64 :max-depth 16
             :max-names 256 :max-name-nodes 16 :max-name-chars 128 :max-total-name-chars 8192})
(defn name-of [text] ["str" ["anonymous"] text])
(defn reference [node] (select-keys node [:module :version]))
(defn node [text dependencies constants extras]
  {:module (name-of text) :version (Object.) :dependencies (mapv reference dependencies)
   :const-names (mapv name-of constants) :extra-names (mapv name-of extras)})
(def native [{:module (name-of "InitBase") :const-names [(name-of "Nat")] :extra-names [(name-of "nativeExtra")]}
             {:module (name-of "Init") :const-names [(name-of "Unit")] :extra-names []}])
(def a (node "A" [] ["A.value"] ["A.helper"]))
(def b (node "B" [a] ["B.value"] []))
(def c (node "C" [b] ["C.value"] []))
(defn reason [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo error (:reason (ex-data error)))))

(deftest chain-importing-c-selects-all-three-modules
  (let [p (graph/plan native [c a b] [(reference c)] limits)]
    (is (= (mapv :module [a b c]) (:source-order p)))
    (is (= (into (mapv :module native) (map :module [a b c])) (:module-order p)))
    (is (= [2 3 4] (mapv (:module-indices p) (map :module [a b c]))))
    (doseq [[module index] [[a 2] [b 3] [c 4]]]
      (is (= {:module (:module module) :module-index index :kind :constant}
             (get-in p [:name-attribution (first (:const-names module))]))))
    (is (= 3 (get-in p [:counts :selected-source-modules])))))

(deftest diamond-deduplicates-by-selected-version-in-actual-header-order
  (let [right (node "Right" [a] ["Right.value"] [])
        left (node "Left" [a] ["Left.value"] [])
        d (node "D" [right left] ["D.value"] [])
        p (graph/plan native [left d a right] [(reference d)] limits)
        reversed (graph/plan native [left d a right] [(reference left) (reference right)] limits)]
    (is (= (mapv :module [a right left d]) (:source-order p)))
    (is (= (mapv :module [a left right]) (:source-order reversed)))
    (is (= 3 (get-in p [:module-indices (:module right)])))
    (is (= 4 (get-in reversed [:module-indices (:module right)])))
    (is (= (:source-order p)
           (:source-order (graph/plan native [d right a left] [(reference d) (reference d)] limits))))
    (is (= 1 (count (filter #{(:module a)} (:source-order p)))))))

(deftest same-shaped-version-tokens-never-replace-the-selected-version
  (let [one (String. "same") two (String. "same")
        a1 (assoc a :version one) a2 (assoc a :version two)
        b1 (assoc b :dependencies [(reference a1)])
        c2 (node "C2" [a2] ["C2.value"] [])
        old (graph/plan native [a1 b1] [(reference b1)] limits)]
    (is (= one two)) (is (not (identical? one two)))
    (is (= :version-conflict (reason #(graph/plan native [a2 b1] [(reference b1)] limits))))
    (is (= :version-conflict (reason #(graph/plan native [a1 b1 c2]
                                                   [(reference b1) (reference c2)] limits))))
    (is (= old (graph/plan native [a1 b1] [(reference b1)] limits))))
  (is (= :duplicate-module (reason #(graph/plan native [a (assoc a :version (Object.))]
                                                [(reference a)] limits)))))

(deftest const-extra-and-native-attribution-collisions-reject
  (doseq [[nodes root] [[[a (assoc b :const-names (:const-names a))] b]
                        [[a (assoc b :extra-names (:extra-names a))] b]
                        [[(assoc a :extra-names (:const-names b)) b] b]
                        [[(assoc a :const-names [(name-of "nativeExtra")])] a]
                        [[(assoc a :extra-names [(name-of "Nat")])] a]]]
    (is (= :attribution-conflict (reason #(graph/plan native nodes [(reference root)] limits)))))
  (doseq [key [:const-names :extra-names]]
    (let [bad (assoc a key [(name-of "duplicate") (name-of "duplicate")])]
      (is (= :duplicate-local-name (reason #(graph/plan native [bad] [(reference bad)] limits))))))
  (let [same-node (assoc a :extra-names (:const-names a))
        p (graph/plan native [same-node] [(reference same-node)] limits)]
    (is (= :constant (get-in p [:name-attribution (first (:const-names a)) :kind]))))
  ;; Native prefix attribution was already attested. Preserve pinned first-wins
  ;; order, including an earlier extra name before a later native CI.
  (let [n [{:module (name-of "NativeFirst") :const-names [] :extra-names [(name-of "shared")]}
           {:module (name-of "NativeLater") :const-names [(name-of "shared")] :extra-names []}]
        p (graph/plan n [] [] limits)]
    (is (= {:module (name-of "NativeFirst") :module-index 0 :kind :extra}
           (get-in p [:name-attribution (name-of "shared")])))))

(deftest missing-cycles-and-unselected-nodes
  (is (= :missing-module (reason #(graph/plan native [b] [(reference b)] limits))))
  (let [cyclic (assoc a :dependencies [(reference b)])]
    (is (= :cycle (reason #(graph/plan native [cyclic b] [(reference b)] limits)))))
  (let [unused (assoc c :dependencies [{:module (name-of "missing") :version (Object.)}])]
    (is (= [(:module a)] (:source-order (graph/plan native [a unused] [(reference a)] limits)))))
  (is (= :duplicate-module
         (reason #(graph/plan native [(assoc a :module (name-of "Init"))] [] limits)))))

(deftest inventory-and-name-bounds-precede-name-hashing-or-traversal
  (is (= :inventory-limit (reason #(graph/plan native [a b] [(reference b)] (assoc limits :max-modules 3)))))
  (is (= :edge-limit (reason #(graph/plan [] [a b c] [(reference c)] (assoc limits :max-edges 1)))))
  (is (= :depth-limit (reason #(graph/plan native [a b c] [(reference c)] (assoc limits :max-depth 2)))))
  (is (= :depth-limit (reason #(graph/plan native [a b c] [(reference b) (reference c)]
                                         (assoc limits :max-depth 2)))))
  (let [poison (proxy [Object] [] (hashCode [] (throw (AssertionError. "Name payload hashed before validation"))))
        bad (assoc a :const-names [["str" ["anonymous"] poison]])]
    (is (= :inventory-limit (reason #(graph/plan [] [bad] [(reference bad)] (assoc limits :max-names 1)))))
    (is (= :name (reason #(graph/plan [] [bad] [(reference bad)] limits))))
    (let [bad-tag (assoc a :const-names [[poison ["anonymous"] "ok"]])]
      (is (= :name (reason #(graph/plan [] [bad-tag] [(reference bad-tag)] limits))))))
  (let [deep (reduce (fn [parent _] ["str" parent "x"]) ["anonymous"] (range 30))
        bad (assoc a :const-names [deep])]
    (is (= :name-limit (reason #(graph/plan [] [bad] [(reference bad)] limits)))))
  (is (= :name-limit (reason #(graph/plan native [a] [(reference a)] (assoc limits :max-name-chars 2)))))
  (let [oversized-module (name-of (str (apply str (repeat 1000 "x")) "."))]
    ;; Dot validation must not run before the constant-time length gate.
    (is (= :name-limit (reason #(graph/plan [] [(assoc a :module oversized-module)] [] limits)))))
  (is (= :name-limit (reason #(graph/plan native [a] [(reference a)] (assoc limits :max-total-name-chars 2)))))
  (doseq [module [["anonymous"] ["num" ["anonymous"] "3"] (name-of "has.dot") (name-of "")]]
    (is (= :module-name (reason #(graph/plan [] [(assoc a :module module)] [] limits))))))

(deftest numeric-wire-name-payload-is-bounded-and-lossless
  (let [digits "18446744073709551615"
        name ["num" (name-of "literal") digits]
        valid (assoc a :const-names [name])]
    (is (= 0 (get-in (graph/plan [] [valid] [(reference valid)] limits)
                     [:name-attribution name :module-index]))))
  (doseq [part [0 -1 "-1" "+1" "01" "" "1e3" "١"]]
    (let [bad (assoc a :const-names [["num" ["anonymous"] part]])]
      (is (= :name (reason #(graph/plan [] [bad] [(reference bad)] limits))))))
  (let [oversized (apply str (repeat 10000 "9"))
        bad (assoc a :const-names [["num" ["anonymous"] oversized]])]
    (is (= :name-limit (reason #(graph/plan [] [bad] [(reference bad)] limits))))))

(deftest deep-chain-planning-does-not-use-the-jvm-call-stack
  (let [count 2000
        names (mapv #(name-of (str "Module" %)) (range count))
        tokens (mapv (fn [_] (Object.)) names)
        nodes (mapv (fn [i]
                      {:module (nth names i) :version (nth tokens i)
                       :dependencies (if (zero? i) [] [{:module (nth names (dec i)) :version (nth tokens (dec i))}])
                       :const-names [] :extra-names []}) (range count))
        capacity (assoc limits :max-modules 2500 :max-edges 2500 :max-depth 2500
                               :max-names 10000 :max-total-name-chars 100000)
        p (graph/plan [] nodes [(reference (peek nodes))] capacity)]
    (is (= names (:source-order p)))
    (is (= count (get-in p [:counts :selected-source-modules])))
    (is (= :depth-limit
           (reason #(graph/plan [] nodes [(reference (nth nodes (- count 2))) (reference (peek nodes))]
                               (assoc capacity :max-depth (dec count))))))))

(deftest closed-input-shapes-and-limits
  (doseq [bad [(dissoc limits :max-depth) (assoc limits :extra true)
               (assoc limits :max-depth 0) (assoc limits :max-names -1)]]
    (is (contains? #{:shape :limits} (reason #(graph/plan native [a] [(reference a)] bad)))))
  (doseq [bad [(assoc a :unknown true) (dissoc a :version) (assoc a :dependencies (list (reference b)))]]
    (is (contains? #{:shape :inventory-limit} (reason #(graph/plan native [bad] [] limits)))))
  (is (= :version (reason #(graph/plan [] [(assoc a :version nil)] [] limits)))))
