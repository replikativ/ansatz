(require '[ansatz.core :as a])
(a/init! "/var/tmp/ansatz-cslib" "cslib")

(println "\n╔═══════════════════════════════════════════════════════════╗")
(println "║  Kernel-Verified Sorting — Merge Sort on Lists           ║")
(println "║  Inspired by CSLib (Lean 4 Computer Science Library)     ║")
(println "╚═══════════════════════════════════════════════════════════╝\n")

;; ============================================================
;; 1. Merge — combine two sorted lists
;; ============================================================
;; Well-founded recursion with compound measure:
;;   termination_by length(xs) + length(ys)
;; Each recursive call reduces at least one list, so the sum decreases.

(println "━━━ 1. Verified Merge ━━━\n")

(a/defn merge [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  :termination-by (+ (List.length xs) (List.length ys))
  (match xs (List Nat) (List Nat)
    (nil ys)
    (cons [x xs']
      (match ys (List Nat) (List Nat)
        (nil (cons x xs'))
        (cons [y ys']
          (if (<= x y)
            (cons x (merge xs' (cons y ys')))
            (cons y (merge (cons x xs') ys'))))))))

(println "(merge '(1 3 5) '(2 4 6)) =>" (merge '(1 3 5) '(2 4 6)))
(println "(merge '() '(1 2))         =>" (merge '() '(1 2)))
(println "(merge '(1) '())           =>" (merge '(1) '()))

;; ============================================================
;; 2. Take / Drop — split a list at position n
;; ============================================================

(println "\n━━━ 2. Verified Take / Drop ━━━\n")

(a/defn take [n :- Nat, xs :- (List Nat)] (List Nat)
  :termination-by n
  (match n Nat (List Nat)
    (zero nil)
    (succ [k]
      (match xs (List Nat) (List Nat)
        (nil nil)
        (cons [hd tl] (cons hd (take k tl)))))))

(a/defn drop [n :- Nat, xs :- (List Nat)] (List Nat)
  :termination-by n
  (match n Nat (List Nat)
    (zero xs)
    (succ [k]
      (match xs (List Nat) (List Nat)
        (nil nil)
        (cons [hd tl] (drop k tl))))))

(println "(take 2 '(1 2 3 4)) =>" (take 2 '(1 2 3 4)))
(println "(drop 2 '(1 2 3 4)) =>" (drop 2 '(1 2 3 4)))

;; ============================================================
;; 3. Merge Sort — recursive divide-and-conquer
;; ============================================================
;; Well-founded recursion with measure: length(xs)
;; Each recursive call operates on half the list.

(println "\n━━━ 3. Verified Merge Sort ━━━\n")

(a/defn sort [xs :- (List Nat)] (List Nat)
  :termination-by (List.length xs)
  (match xs (List Nat) (List Nat)
    (nil nil)
    (cons [hd tl]
      (match tl (List Nat) (List Nat)
        ;; Single element — already sorted
        (nil (cons hd nil))
        ;; Two or more — split, sort recursively, merge
        (cons [hd2 tl2]
          (merge
            (sort (take (/ (+ 2 (List.length tl2)) 2)
                        (cons hd (cons hd2 tl2))))
            (sort (drop (/ (+ 2 (List.length tl2)) 2)
                        (cons hd (cons hd2 tl2))))))))))

(println "(sort '(5 3 1 4 2))     =>" (sort '(5 3 1 4 2)))
(println "(sort '(9 1 8 2 7 3))   =>" (sort '(9 1 8 2 7 3)))
(println "(sort '())              =>" (sort '()))
(println "(sort '(42))            =>" (sort '(42)))
(println "(sort '(2 1))           =>" (sort '(2 1)))

;; ============================================================
;; 4. Structures — Clojure defrecord integration
;; ============================================================

(println "\n━━━ 4. Verified Structures (→ defrecord) ━━━\n")

(a/structure Point [] (x Nat) (y Nat))

(a/defn manhattan [p :- Point] Nat (+ (:x p) (:y p)))

(let [p (->Point 3 4)]
  (println "Point:      " p)
  (println "(:x p)      =" (:x p))
  (println "(manhattan p)=" (manhattan p)))

;; ============================================================
;; 5. Factorial — classic WF recursion
;; ============================================================

(println "\n━━━ 5. Verified Factorial (Well-Founded Recursion) ━━━\n")

(a/defn fact [n :- Nat] Nat
  :termination-by n
  (if (== n 0) 1 (* n (fact (- n 1)))))

(doseq [n (range 8)]
  (println (str "(fact " n ") = " (fact n))))

;; ============================================================
;; 6. Verified Insertion Sort with Correctness Proof
;; ============================================================

(println "\n━━━ 6. Insertion Sort + Correctness Proof ━━━\n")

(a/defn insertSorted [x :- Nat, l :- (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil (cons x nil))
    (cons [hd tl] (match (<= x hd) Bool (List Nat)
      (true (cons x l)) (false (cons hd ih_tail))))))

(a/defn isort [l :- (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil nil)
    (cons [hd tl] (insertSorted hd ih_tail))))

(println "(isort '(5 3 1 4 2)) =>" (isort '(5 3 1 4 2)))

;; Define Sorted as a Prop-valued indexed inductive:
;;   Sorted : List Nat → Prop
(a/inductive Sorted [] :in Prop :indices [l (List Nat)]
  (nil :where [(nil)])
  (single [a Nat] :where [(cons a nil)])
  (cons_cons [a Nat] [b Nat] [tl (List Nat)]
             [hab (le a b)] [hsorted (Sorted (cons b tl))]
    :where [(cons a (cons b tl))]))

;; THE CORRECTNESS THEOREM:
;; "Inserting into a sorted list preserves sortedness"
;;
;; grind handles all 3 induction cases automatically:
;;   nil       → constructor (Sorted.single)
;;   single    → case-split on x<=a, simp, constructor + omega
;;   cons_cons → nested case-splits on x<=a and x<=b, constructors + IH + omega
(a/theorem insert-preserves
  [x :- Nat, l :- (List Nat), h :- (Sorted l)]
  (Sorted (insertSorted x l))
  (induction h)
  (grind "insertSorted"))

(println "✓ Proved: Sorted l → Sorted(insertSorted x l)")
(println "  (kernel-verified by CIC type checker)")

;; ============================================================
;; 7. Manual Proof (for comparison)
;; ============================================================
;; The same theorem proved step-by-step without grind.
;; Each tactic line corresponds to a specific proof obligation.

(println "\n━━━ 7. Same Proof — Manual Tactics (for comparison) ━━━\n")

(a/theorem insert-preserves-manual
  [x :- Nat, l :- (List Nat), h :- (Sorted l)]
  (Sorted (insertSorted x l))
  ;; Induction on h : Sorted l (3 cases: nil, single, cons_cons)
  (induction h)
  ;; Nil case: insertSorted x [] = [x], need Sorted.single
  (apply (Sorted.single x))
  ;; Case-split on x <= a, unfold insertSorted in each branch
  (all_goals (try (by_cases (<= x a))))
  (all_goals (try (simp_all "insertSorted")))
  ;; Sub-split cons_cons case on x <= b
  (all_goals (try (by_cases (<= x b))))
  (all_goals (try (simp_all "insertSorted")))
  (all_goals (try (simp_all "insertSorted")))
  ;; Close remaining: constructors + arithmetic + assumptions
  (all_goals (try (apply Sorted.cons_cons)))
  (all_goals (try (omega)))
  (all_goals (try (apply Sorted.single)))
  (all_goals (try (assumption)))
  (all_goals (try (apply Sorted.cons_cons)))
  (all_goals (try (omega)))
  (all_goals (try (assumption))))

(println "✓ Same theorem proved with 14 manual tactic lines")
(println "  (grind automates all of this from the induction hypothesis)")

(println "\n━━━ Summary ━━━\n")
(println "All functions and theorems above are:")
(println "  1. Type-checked by the CIC kernel (same type theory as Lean 4)")
(println "  2. Compiled to native Clojure (defrecord, flat calls, persistent lists)")
(println "  3. Equipped with equation theorems for use in proofs")
(println "  4. Termination-verified via fuel-based Nat.rec measures")
(println "  5. Correctness properties formally proved (insertion sort preserves sortedness)")
