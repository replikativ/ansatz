(ns ansatz.grind-conformance-test
  "Paired Init-only Lean grind scripts; see test/lean/grind_conformance.lean.
   Core cases adapt grind_t1/grind_split; list and ownership cases adapt the local probes.
   `induction xs <;> grind [hints]` translates to `and_then` with the same hints.
   Definition names use a gc prefix here (app → gcapp, Own → GCOwn) for isolation.
   Surface if uses Bool.rec, whereas Lean uses ite with a Bool-to-Prop coercion."
  (:require [clojure.test :refer [deftest]]
            [ansatz.conformance-support :as cs]))

(def ^:private defs
  '[(ansatz.core/defn gcapp [xs :- (List Nat), ys :- (List Nat)] (List Nat)
      (match xs [nil ys] [(cons h t) (List.cons Nat h (gcapp t ys))]))
    (ansatz.core/defn gclen [xs :- (List Nat)] Nat
      (match xs [nil 0] [(cons h t) (+ (gclen t) 1)]))
    (ansatz.core/defn gcmap [f :- (=> Nat Nat), xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (f h) (gcmap f t))]))
    (ansatz.core/defn gcfilter [p :- (=> Nat Bool), xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons h t) (if (p h) (List.cons Nat h (gcfilter p t)) (gcfilter p t))]))
    (ansatz.core/structure GCOwn [] (ent Nat) (scope Nat))
    (ansatz.core/defn gcmemq [x :- Nat, xs :- (List Nat)] Bool
      (match xs [nil false] [(cons h t) (if (Nat.beq x h) true (gcmemq x t))]))
    (ansatz.core/defn gcdropNat [x :- Nat, xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)] [(cons h t) (if (Nat.beq h x) (gcdropNat x t) (List.cons Nat h (gcdropNat x t)))]))
    (ansatz.core/defn gcownersOpen [os :- (List GCOwn), op :- (List Nat)] Bool
      (match os [nil true] [(cons o t) (if (gcmemq (:scope o) op) (gcownersOpen t op) false)]))
    (ansatz.core/defn gcdropOwned [sc :- Nat, os :- (List GCOwn)] (List GCOwn)
      (match os [nil (List.nil GCOwn)] [(cons o t) (if (Nat.beq (:scope o) sc) (gcdropOwned sc t) (List.cons GCOwn o (gcdropOwned sc t)))]))])

(def ^:private theorems
  '[[g01_trans [a :- Nat, b :- Nat, c :- Nat, h1 :- (= a b), h2 :- (= b c)]
     (= a c)
     [(grind)]]
    [g02_congr [f :- (=> Nat Nat), a :- Nat, b :- Nat, h :- (= a b)]
     (= (f a) (f b))
     [(grind)]]
    [g03_nested [f :- (=> Nat Nat), g :- (=> Nat Nat), a :- Nat, b :- Nat, c :- Nat, h1 :- (= a c), h2 :- (= b c)]
     (= (f (g a)) (f (g b)))
     [(grind)]]
    [g04_list_clash [a :- (List Nat), b :- (List Nat)]
     (=> (= a (List.nil Nat)) (= b (List.cons Nat 2 (List.nil Nat))) (= a b) False)
     [(grind)]]
    [g05_bool_clash [a :- Bool, b :- Bool]
     (=> (= a true) (= b false) (= a b) False)
     [(grind)]]
    [g06_inject_head [a :- Nat, c :- Nat, b :- (List Nat), d :- (List Nat), h :- (= (List.cons Nat a b) (List.cons Nat c d))]
     (= a c)
     [(grind)]]
    [g07_inject_tail [a :- Nat, c :- Nat, b :- (List Nat), d :- (List Nat), h :- (= (List.cons Nat a b) (List.cons Nat c d))]
     (= b d)
     [(grind)]]
    [g08_and_comm [p :- Prop, q :- Prop]
     (Iff (And p q) (And q p))
     [(grind)]]
    [g09_or_resolve [p :- Prop, q :- Prop, h1 :- (Or p q), h2 :- (Not p)]
     q
     [(grind)]]
    [g10_split_unsat [p :- Prop, q :- Prop]
     (=> (Or p q) (Or p (Not q)) (Or (Not p) q) (Or (Not p) (Not q)) False)
     [(grind)]]
    [g11_modus [p :- Prop, q :- Prop, h1 :- (=> p q), h2 :- p]
     q
     [(grind)]]
    [g12_ematch [f :- (=> Nat Nat), h :- (forall [x :- Nat] (= (f x) x)), a :- Nat]
     (= (f (f a)) a)
     [(grind)]]
    [g13_forward [p :- (=> Nat Prop), q :- (=> Nat Prop), h :- (forall [x :- Nat] (=> (p x) (q x))), a :- Nat, ha :- (p a)]
     (q a)
     [(grind)]]
    [g14_if_true [b :- Bool, x :- Nat, y :- Nat, h :- (= b true)]
     (= (if b x y) x)
     [(grind)]]
    [g15_if_false [b :- Bool, x :- Nat, y :- Nat, h :- (= b false)]
     (= (if b x y) y)
     [(grind)]]
    [g16_beq [a :- Nat, b :- Nat, h :- (= (Nat.beq a b) true)]
     (= a b)
     [(grind [Nat.beq_eq])]]
    [g17_linear [a :- Nat, b :- Nat, h :- (< a b)]
     (Not (< b a))
     [(grind)]]
    [g18_ring [a :- Nat, b :- Nat]
     (= (* (+ a b) (+ a b)) (+ (+ (* a a) (* (* 2 a) b)) (* b b)))
     [(grind)]]
    [g19_app_nil [xs :- (List Nat)]
     (= (gcapp xs (List.nil Nat)) xs)
     [(and_then (induction xs) (grind [gcapp]))]]
    [g20_app_assoc [xs :- (List Nat), ys :- (List Nat), zs :- (List Nat)]
     (= (gcapp (gcapp xs ys) zs) (gcapp xs (gcapp ys zs)))
     [(and_then (induction xs) (grind [gcapp]))]]
    [g21_len_app [xs :- (List Nat), ys :- (List Nat)]
     (= (gclen (gcapp xs ys)) (+ (gclen xs) (gclen ys)))
     [(and_then (induction xs) (grind [gclen gcapp]))]]
    [g22_len_map [f :- (=> Nat Nat), xs :- (List Nat)]
     (= (gclen (gcmap f xs)) (gclen xs))
     [(and_then (induction xs) (grind [gclen gcmap]))]]
    [g23_map_app [f :- (=> Nat Nat), xs :- (List Nat), ys :- (List Nat)]
     (= (gcmap f (gcapp xs ys)) (gcapp (gcmap f xs) (gcmap f ys)))
     [(and_then (induction xs) (grind [gcmap gcapp]))]]
    [g24_map_id [xs :- (List Nat)]
     (= (gcmap (fn [x :- Nat] x) xs) xs)
     [(and_then (induction xs) (grind [gcmap]))]]
    [g25_filter_app [p :- (=> Nat Bool), xs :- (List Nat), ys :- (List Nat)]
     (= (gcfilter p (gcapp xs ys)) (gcapp (gcfilter p xs) (gcfilter p ys)))
     [(and_then (induction xs) (grind [gcfilter gcapp]))]]
    [g26_filter_idem [p :- (=> Nat Bool), xs :- (List Nat)]
     (= (gcfilter p (gcfilter p xs)) (gcfilter p xs))
     [(and_then (induction xs) (grind [gcfilter]))]]
    [g27_filter_len [p :- (=> Nat Bool), xs :- (List Nat)]
     (<= (gclen (gcfilter p xs)) (gclen xs))
     [(and_then (induction xs) (grind [gcfilter gclen]))]]
    [g28_memq_drop [x :- Nat, sc :- Nat, op :- (List Nat)]
     (=> (= (gcmemq x op) true) (= (Nat.beq x sc) false) (= (gcmemq x (gcdropNat sc op)) true))
     [(and_then (induction op) (grind [gcmemq gcdropNat Nat.beq_eq]))]]
    [g29_owners_drop [sc :- Nat, op :- (List Nat), os :- (List GCOwn)]
     (=> (= (gcownersOpen os op) true) (= (gcownersOpen (gcdropOwned sc os) (gcdropNat sc op)) true))
     [(and_then (induction os) (grind [gcownersOpen gcdropOwned Nat.beq_eq g28_memq_drop]))]]
    [g30_owners_hyp [sc :- Nat, op :- (List Nat), os :- (List GCOwn), h :- (= (gcownersOpen os op) true)]
     (= (gcownersOpen (gcdropOwned sc os) (gcdropNat sc op)) true)
     [(and_then (induction os) (grind [gcownersOpen gcdropOwned Nat.beq_eq g28_memq_drop]))]]])

(def ^:private known-gaps
  '{g18_ring "The ring theory solver is deferred beyond the logical core."})

(deftest grind-conformance
  (cs/check-suite "grind"
                  (cs/run-suite 'ansatz.grind-conformance-test defs theorems)
                  known-gaps))
