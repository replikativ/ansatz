(ns ansatz.list-conformance-test
  "Conformance of ansatz's tactics against Lean 4 on everyday proofs: standard list lemmas over
  USER-DEFINED recursive functions (the shape of a verified reference model), each proved with the
  line-by-line translation of the idiomatic Lean script in
  test/lean/list_conformance.lean (all accepted by Lean 4.33).

  Translation rules: `t1 <;> t2` is `(and_then t1 t2)`; `induction xs with | nil => A | cons … => B`
  is `(induction xs) A B` (alternatives come in constructor order; the cons fields are named
  `head`/`tail`/`ih_tail`); `cases h : e` is `(cases h e)`; `simp [a, b]` is `(simp [a b])`;
  `p x && q x` is `(Bool.and (p x) (q x))`."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]))

(def ^:private defs
  '[(ansatz.core/defn mylen [xs :- (List Nat)] Nat
      (match xs [nil 0] [(cons h t) (+ (mylen t) 1)]))
    (ansatz.core/defn myapp [xs :- (List Nat), ys :- (List Nat)] (List Nat)
      (match xs [nil ys] [(cons h t) (List.cons Nat h (myapp t ys))]))
    (ansatz.core/defn myrev [xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons h t) (myapp (myrev t) (List.cons Nat h (List.nil Nat)))]))
    (ansatz.core/defn mymap [f :- (=> Nat Nat), xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (f h) (mymap f t))]))
    (ansatz.core/defn myfilter [p :- (=> Nat Bool), xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons h t) (if (p h) (List.cons Nat h (myfilter p t)) (myfilter p t))]))
    (ansatz.core/defn mysum [xs :- (List Nat)] Nat
      (match xs [nil 0] [(cons h t) (+ h (mysum t))]))
    (ansatz.core/defn mymem [x :- Nat, xs :- (List Nat)] Bool
      (match xs [nil false] [(cons h t) (if (Nat.beq x h) true (mymem x t))]))
    (ansatz.core/defn mycount [x :- Nat, xs :- (List Nat)] Nat
      (match xs [nil 0] [(cons h t) (if (Nat.beq x h) (+ (mycount x t) 1) (mycount x t))]))
    (ansatz.core/defn myall [p :- (=> Nat Bool), xs :- (List Nat)] Bool
      (match xs [nil true] [(cons h t) (if (p h) (myall p t) false)]))])

(def ^:private theorems
  "[name params statement tactics] in dependency order — the Lean scripts, translated."
  '[[c01_app_nil [xs :- (List Nat)] (= (myapp xs (List.nil Nat)) xs)
     [(and_then (induction xs) (simp [myapp *]))]]
    [c02_app_assoc [xs :- (List Nat), ys :- (List Nat), zs :- (List Nat)]
     (= (myapp (myapp xs ys) zs) (myapp xs (myapp ys zs)))
     [(and_then (induction xs) (simp [myapp *]))]]
    [c03_len_app [xs :- (List Nat), ys :- (List Nat)] (= (mylen (myapp xs ys)) (+ (mylen xs) (mylen ys)))
     [(and_then (and_then (induction xs) (simp [mylen myapp *])) (omega))]]
    [c04_len_map [f :- (=> Nat Nat), xs :- (List Nat)] (= (mylen (mymap f xs)) (mylen xs))
     [(and_then (induction xs) (simp [mylen mymap *]))]]
    [c05_map_app [f :- (=> Nat Nat), xs :- (List Nat), ys :- (List Nat)]
     (= (mymap f (myapp xs ys)) (myapp (mymap f xs) (mymap f ys)))
     [(and_then (induction xs) (simp [mymap myapp *]))]]
    [c06_rev_app [xs :- (List Nat), ys :- (List Nat)] (= (myrev (myapp xs ys)) (myapp (myrev ys) (myrev xs)))
     [(and_then (induction xs) (simp [myrev myapp c01_app_nil c02_app_assoc *]))]]
    [c07_rev_rev [xs :- (List Nat)] (= (myrev (myrev xs)) xs)
     [(and_then (induction xs) (simp [myrev myapp c06_rev_app *]))]]
    [c08_len_rev [xs :- (List Nat)] (= (mylen (myrev xs)) (mylen xs))
     [(and_then (induction xs) (simp [myrev mylen c03_len_app *]))]]
    [c09_filter_app [p :- (=> Nat Bool), xs :- (List Nat), ys :- (List Nat)]
     (= (myfilter p (myapp xs ys)) (myapp (myfilter p xs) (myfilter p ys)))
     [(induction xs)
      (simp [myfilter myapp])
      (and_then (cases hp (p head)) (simp [myfilter myapp hp ih_tail]))]]
    [c10_len_filter_le [p :- (=> Nat Bool), xs :- (List Nat)] (<= (mylen (myfilter p xs)) (mylen xs))
     [(induction xs)
      (simp [myfilter mylen])
      (and_then (and_then (cases hp (p head)) (simp [myfilter mylen hp])) (omega))]]
    [c11_sum_app [xs :- (List Nat), ys :- (List Nat)] (= (mysum (myapp xs ys)) (+ (mysum xs) (mysum ys)))
     [(and_then (and_then (induction xs) (simp [mysum myapp *])) (omega))]]
    [c12_mem_app [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
     (= (mymem x (myapp xs ys)) (Bool.or (mymem x xs) (mymem x ys)))
     [(induction xs)
      (simp [mymem myapp])
      (and_then (cases hx (Nat.beq x head)) (simp [mymem myapp hx ih_tail]))]]
    [c13_filter_filter [p :- (=> Nat Bool), q :- (=> Nat Bool), xs :- (List Nat)]
     (= (myfilter p (myfilter q xs)) (myfilter (fn [x :- Nat] (Bool.and (p x) (q x))) xs))
     [(induction xs)
      (simp [myfilter])
      (and_then (and_then (cases hq (q head)) (cases hp (p head))) (simp [myfilter hp hq ih_tail]))]]
    [c14_all_filter [p :- (=> Nat Bool), xs :- (List Nat)] (= (myall p (myfilter p xs)) true)
     [(induction xs)
      (simp [myfilter myall])
      (and_then (cases hp (p head)) (simp [myfilter myall hp ih_tail]))]]
    [c15_count_le_len [x :- Nat, xs :- (List Nat)] (<= (mycount x xs) (mylen xs))
     [(induction xs)
      (simp [mycount mylen])
      (and_then (and_then (cases hx (Nat.beq x head)) (simp [mycount mylen hx])) (omega))]]
    [c16_mem_filter [p :- (=> Nat Bool), x :- Nat, xs :- (List Nat)]
     (=> (= (mymem x (myfilter p xs)) true) (= (mymem x xs) true))
     [(induction xs)
      (simp [myfilter mymem])
      (intro hm)
      (and_then (and_then (cases hp (p head)) (cases hx (Nat.beq x head))) (simp_all [myfilter mymem]))]]
    [c17_map_id [xs :- (List Nat)] (= (mymap (fn [x :- Nat] x) xs) xs)
     [(and_then (induction xs) (simp [mymap *]))]]
    [c18_mem_app_left [x :- Nat, xs :- (List Nat), ys :- (List Nat), h :- (= (mymem x xs) true)]
     (= (mymem x (myapp xs ys)) true)
     [(induction xs)
      (simp [mymem] at h)
      (and_then (cases hx (Nat.beq x head)) (simp_all [mymem myapp]))]]
    [c19_closed [] (= (mylen (myrev (List.cons Nat 1 (List.cons Nat 2 (List.cons Nat 3 (List.nil Nat)))))) 3)
     [(decide)]]
    [c20_sum_rev [xs :- (List Nat)] (= (mysum (myrev xs)) (mysum xs))
     [(and_then (and_then (induction xs) (simp [myrev mysum c11_sum_app *])) (omega))]]])

(defn- attempt
  "Prove one theorem with a time budget; :ok, or the failure message."
  [[nm params stmt tactics] timeout-ms]
  (let [f (future (try (a/prove-theorem nm params stmt tactics) :ok
                       (catch Throwable t (or (.getMessage t) (str (class t))))))
        r (deref f timeout-ms ::timeout)]
    (when (= ::timeout r) (future-cancel f))
    (if (= ::timeout r) (str "timeout after " timeout-ms " ms") r)))

(defn run-conformance
  "Define the functions on a fresh Init env and attempt every theorem in order. Returns
   [[name result] …]. Usable from the REPL to see the current score."
  []
  (a/load-init!)
  (binding [a/*verbose* false
            *ns* (the-ns 'ansatz.list-conformance-test)]
    (run! eval defs)
    (mapv (fn [t] [(first t) (attempt t 60000)]) theorems)))

(deftest list-conformance
  (let [results (run-conformance)
        passed (count (filter #(= :ok (second %)) results))]
    (println (str "list conformance: " passed "/" (count results) " Lean scripts go through"))
    (doseq [[nm r] results :when (not= :ok r)]
      (println " " nm "-" (subs r 0 (min 160 (count r)))))
    (doseq [[nm r] results]
      (testing (str nm) (is (= :ok r))))))
