-- Lean 4 reference for test/ansatz/list_conformance_test.clj: standard list lemmas over
-- USER-DEFINED recursive functions, each with the idiomatic Lean proof. Every theorem is accepted
-- by Lean 4.33 (lean-lsp lean_run_code, 2026-10-26). The ansatz test states the same theorems
-- with the line-by-line translation of these scripts and records which go through.
def mylen : List Nat → Nat
  | [] => 0
  | _ :: t => mylen t + 1
def myapp : List Nat → List Nat → List Nat
  | [], ys => ys
  | h :: t, ys => h :: myapp t ys
def myrev : List Nat → List Nat
  | [] => []
  | h :: t => myapp (myrev t) [h]
def mymap (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | h :: t => f h :: mymap f t
def myfilter (p : Nat → Bool) : List Nat → List Nat
  | [] => []
  | h :: t => if p h then h :: myfilter p t else myfilter p t
def mysum : List Nat → Nat
  | [] => 0
  | h :: t => h + mysum t
def mymem (x : Nat) : List Nat → Bool
  | [] => false
  | h :: t => if Nat.beq x h then true else mymem x t
def mycount (x : Nat) : List Nat → Nat
  | [] => 0
  | h :: t => if Nat.beq x h then mycount x t + 1 else mycount x t
def myall (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | h :: t => if p h then myall p t else false

theorem c01_app_nil (xs : List Nat) : myapp xs [] = xs := by
  induction xs <;> simp [myapp, *]
theorem c02_app_assoc (xs ys zs : List Nat) : myapp (myapp xs ys) zs = myapp xs (myapp ys zs) := by
  induction xs <;> simp [myapp, *]
theorem c03_len_app (xs ys : List Nat) : mylen (myapp xs ys) = mylen xs + mylen ys := by
  induction xs <;> simp [mylen, myapp, *] <;> omega
theorem c04_len_map (f : Nat → Nat) (xs : List Nat) : mylen (mymap f xs) = mylen xs := by
  induction xs <;> simp [mylen, mymap, *]
theorem c05_map_app (f : Nat → Nat) (xs ys : List Nat) : mymap f (myapp xs ys) = myapp (mymap f xs) (mymap f ys) := by
  induction xs <;> simp [mymap, myapp, *]
theorem c06_rev_app (xs ys : List Nat) : myrev (myapp xs ys) = myapp (myrev ys) (myrev xs) := by
  induction xs <;> simp [myrev, myapp, c01_app_nil, c02_app_assoc, *]
theorem c07_rev_rev (xs : List Nat) : myrev (myrev xs) = xs := by
  induction xs <;> simp [myrev, myapp, c06_rev_app, *]
theorem c08_len_rev (xs : List Nat) : mylen (myrev xs) = mylen xs := by
  induction xs <;> simp [myrev, mylen, c03_len_app, *]
theorem c09_filter_app (p : Nat → Bool) (xs ys : List Nat) : myfilter p (myapp xs ys) = myapp (myfilter p xs) (myfilter p ys) := by
  induction xs with
  | nil => simp [myfilter, myapp]
  | cons h t ih => cases hp : p h <;> simp [myfilter, myapp, hp, ih]
theorem c10_len_filter_le (p : Nat → Bool) (xs : List Nat) : mylen (myfilter p xs) ≤ mylen xs := by
  induction xs with
  | nil => simp [myfilter, mylen]
  | cons h t ih => cases hp : p h <;> simp [myfilter, mylen, hp] <;> omega
theorem c11_sum_app (xs ys : List Nat) : mysum (myapp xs ys) = mysum xs + mysum ys := by
  induction xs <;> simp [mysum, myapp, *] <;> omega
theorem c12_mem_app (x : Nat) (xs ys : List Nat) : mymem x (myapp xs ys) = (mymem x xs || mymem x ys) := by
  induction xs with
  | nil => simp [mymem, myapp]
  | cons h t ih => cases hx : Nat.beq x h <;> simp [mymem, myapp, hx, ih]
theorem c13_filter_filter (p q : Nat → Bool) (xs : List Nat) : myfilter p (myfilter q xs) = myfilter (fun x => p x && q x) xs := by
  induction xs with
  | nil => simp [myfilter]
  | cons h t ih => cases hq : q h <;> cases hp : p h <;> simp [myfilter, hp, hq, ih]
theorem c14_all_filter (p : Nat → Bool) (xs : List Nat) : myall p (myfilter p xs) = true := by
  induction xs with
  | nil => simp [myfilter, myall]
  | cons h t ih => cases hp : p h <;> simp [myfilter, myall, hp, ih]
theorem c15_count_le_len (x : Nat) (xs : List Nat) : mycount x xs ≤ mylen xs := by
  induction xs with
  | nil => simp [mycount, mylen]
  | cons h t ih => cases hx : Nat.beq x h <;> simp [mycount, mylen, hx] <;> omega
theorem c16_mem_filter (p : Nat → Bool) (x : Nat) (xs : List Nat) : mymem x (myfilter p xs) = true → mymem x xs = true := by
  induction xs with
  | nil => simp [myfilter, mymem]
  | cons h t ih =>
    intro hm
    cases hp : p h <;> cases hx : Nat.beq x h <;> simp_all [myfilter, mymem]
theorem c17_map_id (xs : List Nat) : mymap (fun x => x) xs = xs := by
  induction xs <;> simp [mymap, *]
theorem c18_mem_app_left (x : Nat) (xs ys : List Nat) (h : mymem x xs = true) : mymem x (myapp xs ys) = true := by
  induction xs with
  | nil => simp [mymem] at h
  | cons a t ih => cases hx : Nat.beq x a <;> simp_all [mymem, myapp]
theorem c19_closed : mylen (myrev [1, 2, 3]) = 3 := by decide
theorem c20_sum_rev (xs : List Nat) : mysum (myrev xs) = mysum xs := by
  induction xs <;> simp [myrev, mysum, c11_sum_app, *] <;> omega
