(ns ansatz.codegen-nested-match-test
  "Nested matches compile in time linear in their depth. Codegen used to compile every
   argument of an application before choosing a lowering; a match auxiliary is unfolded and a
   recursor's minors are compiled from their kernel terms, so that work was discarded and each
   nesting level compiled its inner matches again (5 levels: 18 s, now 0.2 s)."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f]
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.codegen-nested-match-test)]
      (a/load-init!)
      (a/inductive NmShape [] (a) (b [x Nat]) (c [x Nat] [y Nat]) (d [t NmShape]))
      (f))))

(defn- nested-body
  "match v_{depth-1} … match v0, each level falling through `d` to the next."
  [depth]
  (reduce (fn [inner i]
            (list 'match (symbol (str "v" i))
                  '[a 0] '[(b x) x] '[(c x y) (+ x y)] ['(d t) inner]))
          1 (range depth)))

(defn- define! [depth]
  (let [nm (gensym (str "nm-nest-" depth "-"))
        params (vec (mapcat (fn [i] [(symbol (str "v" i)) :- 'NmShape]) (range depth)))]
    (binding [*ns* (the-ns 'ansatz.codegen-nested-match-test)]
      (eval (list 'ansatz.core/defn nm params 'Nat (nested-body depth))))
    @(ns-resolve 'ansatz.codegen-nested-match-test nm)))

(defn- codegen-calls [depth]
  (let [n (atom 0) f cg/ansatz->clj]
    (with-redefs [cg/ansatz->clj (fn [& xs] (swap! n inc) (apply f xs))]
      (define! depth))
    @n))

(deftest nested-match-codegen-is-linear-in-depth
  (let [c3 (codegen-calls 3) c6 (codegen-calls 6)]
    ;; linear growth doubles the work from depth 3 to 6; eager argument compilation
    ;; multiplied it by roughly 4 per level (≈ 64×)
    (is (< c6 (* 4 c3)) (str "codegen calls: depth 3 = " c3 ", depth 6 = " c6))))

(deftest nested-match-results
  (let [f2 (define! 2) f3 (define! 3)]
    ;; tagged representation [cidx field…]: a = [0], b x = [1 x], c x y = [2 x y], d t = [3 t]
    (is (= 7 (f2 [1 7] [3 [0]])))
    (is (= 5 (f2 [1 7] [2 2 3])))
    (is (= 0 (f2 [0] [3 [0]])))
    (is (= 1 (f2 [3 [0]] [3 [0]])))
    (is (= 9 (f3 [2 4 5] [3 [0]] [3 [0]])))))
