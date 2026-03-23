(require '[ansatz.core :as a])
(a/init! "/var/tmp/ansatz-cslib" "cslib")

(println "\n========================================================")
(println "  Verified List Library — Kernel-Checked Clojure")
(println "  Inspired by CSLib (Lean 4 Computer Science Library)")
(println "========================================================\n")

;; ============================================================
;; 1. Core Operations — all kernel-verified, compile to Clojure
;; ============================================================

(println "--- Definitions ---\n")

;; map: apply a function to every element
(a/defn lmap [f :- (arrow Nat Nat), l :- (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil nil)
    (cons [hd tl] (cons (f hd) ih_tail))))

;; filter: keep elements satisfying a predicate
(a/defn lfilter [p :- (arrow Nat Bool), l :- (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil nil)
    (cons [hd tl] (match (p hd) Bool (List Nat)
      (true (cons hd ih_tail))
      (false ih_tail)))))

;; length
(a/defn llen [l :- (List Nat)] Nat
  (match l (List Nat) Nat
    (nil 0)
    (cons [_ tl] (+ 1 ih_tail))))

;; append
(a/defn lappend [xs :- (List Nat), ys :- (List Nat)] (List Nat)
  (match xs (List Nat) (List Nat)
    (nil ys)
    (cons [hd tl] (cons hd ih_tail))))

;; nth with default
(a/defn lnth [l :- (List Nat), n :- Nat, d :- Nat] Nat
  (match l (List Nat) Nat
    (nil d)
    (cons [hd tl] (match n Nat Nat
      (zero hd)
      (succ [k] ih_tail)))))

;; all: check predicate holds for all elements
(a/defn lall [p :- (arrow Nat Bool), l :- (List Nat)] Bool
  (match l (List Nat) Bool
    (nil true)
    (cons [hd tl] (match (p hd) Bool Bool
      (true ih_tail)
      (false false)))))

;; any: check predicate holds for some element
(a/defn lany [p :- (arrow Nat Bool), l :- (List Nat)] Bool
  (match l (List Nat) Bool
    (nil false)
    (cons [hd tl] (match (p hd) Bool Bool
      (true true)
      (false ih_tail)))))

;; --- Demo ---
(println "(lmap inc '(1 2 3))          =>" (lmap inc '(1 2 3)))
(println "(lfilter even? '(1 2 3 4 5)) =>" (lfilter even? '(1 2 3 4 5)))
(println "(llen '(1 2 3))              =>" (llen '(1 2 3)))
(println "(lappend '(1 2) '(3 4))      =>" (lappend '(1 2) '(3 4)))
(println "(lnth '(10 20 30) 1 0)       =>" (lnth '(10 20 30) 1 0))
(println "(lall pos? '(1 2 3))         =>" (lall pos? '(1 2 3)))
(println "(lany even? '(1 3 4))        =>" (lany even? '(1 3 4)))

;; ============================================================
;; 2. Verified Properties — all proved by grind, kernel-checked
;; ============================================================

(println "\n--- Proofs (all kernel-verified) ---\n")

;; Nil identities
(a/theorem llen-nil [] (= Nat (llen nil) 0) (grind "llen"))
(println "  llen []           = 0")

(a/theorem lappend-nil-left [ys :- (List Nat)]
  (= (List Nat) (lappend nil ys) ys) (grind "lappend"))
(println "  lappend [] ys     = ys")

(a/theorem lmap-nil [f :- (arrow Nat Nat)]
  (= (List Nat) (lmap f nil) nil) (grind "lmap"))
(println "  lmap f []         = []")

(a/theorem lfilter-nil [p :- (arrow Nat Bool)]
  (= (List Nat) (lfilter p nil) nil) (grind "lfilter"))
(println "  lfilter p []      = []")

(a/theorem lall-nil [p :- (arrow Nat Bool)]
  (= Bool (lall p nil) Bool.true) (grind "lall"))
(println "  lall p []         = true")

(a/theorem lany-nil [p :- (arrow Nat Bool)]
  (= Bool (lany p nil) Bool.false) (grind "lany"))
(println "  lany p []         = false")

(a/theorem lnth-nil [n :- Nat, d :- Nat]
  (= Nat (lnth nil n d) d) (grind "lnth"))
(println "  lnth [] n d       = d")

;; Structural properties (induction + grind)
(a/theorem lappend-assoc [xs :- (List Nat), ys :- (List Nat), zs :- (List Nat)]
  (= (List Nat) (lappend (lappend xs ys) zs) (lappend xs (lappend ys zs)))
  (induction xs) (grind "lappend"))
(println "  (xs++ys)++zs      = xs++(ys++zs)    [append associativity]")

(a/theorem lappend-nil-right [xs :- (List Nat)]
  (= (List Nat) (lappend xs nil) xs)
  (induction xs) (all_goals (try (simp_all "lappend"))) (all_goals (try (grind "lappend"))))
(println "  xs++[]            = xs               [append right identity]")

;; Constructor discrimination
(a/theorem cons-ne-nil [x :- Nat, xs :- (List Nat),
                         h :- (= (List Nat) (cons x xs) nil)]
  False (grind))
(println "  x::xs != []                          [constructor discrimination]")

;; ============================================================
;; 3. Insertion Sort with Correctness Proof
;; ============================================================

(println "\n--- Insertion Sort + Correctness ---\n")

(a/defn insertSorted [x :- Nat, l :- (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil (cons x nil))
    (cons [hd tl] (match (<= x hd) Bool (List Nat)
      (true (cons x l)) (false (cons hd ih_tail))))))

(a/defn isort [l :- (List Nat)] (List Nat)
  (match l (List Nat) (List Nat)
    (nil nil)
    (cons [hd tl] (insertSorted hd ih_tail))))

(println "(isort '(5 3 1 4 2))  =>" (isort '(5 3 1 4 2)))

;; Sorted predicate (indexed inductive)
(a/inductive Sorted [] :in Prop :indices [l (List Nat)]
  (nil :where [(nil)])
  (single [a Nat] :where [(cons a nil)])
  (cons_cons [a Nat] [b Nat] [tl (List Nat)]
             [hab (le a b)] [hsorted (Sorted (cons b tl))]
    :where [(cons a (cons b tl))]))

;; THE THEOREM: inserting into a sorted list preserves sortedness
;; grind handles all 3 induction cases automatically
(a/theorem insert-preserves
  [x :- Nat, l :- (List Nat), h :- (Sorted l)]
  (Sorted (insertSorted x l))
  (induction h)
  (grind "insertSorted"))

(println "  Sorted l -> Sorted (insertSorted x l)  [grind, 2 lines]")

(println "\n========================================================")
(println "  All definitions are:")
(println "    1. Type-checked by the CIC kernel")
(println "    2. Compiled to native Clojure functions")
(println "    3. Properties formally proved with grind")
(println "    4. Proofs kernel-verified (no trusted axioms)")
(println "========================================================")
