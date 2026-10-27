-- Lean 4.33.1 reference; paired with test/ansatz/prop_inductive_conformance_test.clj.
-- Scripts follow Lean.Elab.Tactic.Induction.evalInductionCore/evalCasesCore,
-- Simp.evalSimp and Decide.evalDecideCore in src/Lean/Elab/Tactic/.
set_option linter.unusedSimpArgs false
inductive Mem (x : Nat) : List Nat → Prop where
  | head (t : List Nat) : Mem x (x :: t)
  | tail (y : Nat) (t : List Nat) (h : Mem x t) : Mem x (y :: t)
inductive All (p : Nat → Prop) : List Nat → Prop where
  | nil : All p []
  | cons (x : Nat) (xs : List Nat) (hx : p x) (ht : All p xs) : All p (x :: xs)
inductive Sorted : Nat → List Nat → Prop where
  | nil (n : Nat) : Sorted n []
  | cons (n x : Nat) (xs : List Nat) (hx : n ≤ x) (ht : Sorted x xs) : Sorted n (x :: xs)
inductive Reach (r : Nat → Nat → Prop) : Nat → Nat → Prop where
  | refl (x : Nat) : Reach r x x
  | step (x y z : Nat) (hxy : r x y) (hyz : Reach r y z) : Reach r x z

theorem p01_mem_head (x : Nat) (xs : List Nat) : Mem x (x :: xs) := by
  constructor

theorem p02_mem_tail (x y : Nat) (xs : List Nat) (h : Mem x xs) : Mem x (y :: xs) := by
  exact @Mem.tail x y xs h

theorem p03_mem_nil (x : Nat) (h : Mem x []) : False := by
  cases h

theorem p04_all_nil (p : Nat → Prop) : All p [] := by
  simp [All.nil]

theorem p05_all_cons (p : Nat → Prop) (x : Nat) (xs : List Nat) (hx : p x) (ht : All p xs) : All p (x :: xs) := by
  constructor
  exact hx
  exact ht

theorem p06_all_head (p : Nat → Prop) (x : Nat) (xs : List Nat) (h : All p (x :: xs)) : p x := by
  cases h with
  | cons a t ha ht => exact ha

theorem p07_all_tail (p : Nat → Prop) (x : Nat) (xs : List Nat) (h : All p (x :: xs)) : All p xs := by
  cases h with
  | cons a t ha ht => exact ht

theorem p08_all_true (xs : List Nat) : All (fun _ => True) xs := by
  induction xs with
  | nil => constructor
  | cons x xs ih => constructor; trivial; exact ih

theorem p09_all_nonneg (xs : List Nat) : All (fun x => 0 ≤ x) xs := by
  induction xs with
  | nil => constructor
  | cons x xs ih => constructor; omega; exact ih

theorem p10_sorted_nil (n : Nat) : Sorted n [] := by
  constructor

theorem p11_sorted_single (n x : Nat) (h : n ≤ x) : Sorted n [x] := by
  constructor
  exact h
  constructor

theorem p12_sorted_head (n x : Nat) (xs : List Nat) (h : Sorted n (x :: xs)) : n ≤ x := by
  cases h with
  | cons a b t hx ht => exact hx

theorem p13_reach_refl (r : Nat → Nat → Prop) (x : Nat) : Reach r x x := by
  constructor

theorem p14_reach_one (r : Nat → Nat → Prop) (x y : Nat) (h : r x y) : Reach r x y := by
  exact @Reach.step r x y y h (@Reach.refl r y)

theorem p15_reach_eq (x y : Nat) (h : Reach Eq x y) : x = y := by
  induction h with
  | refl a => rfl
  | step a b c hab hbc ih => simp_all
