-- Lean 4.33.1 reference; paired with test/ansatz/option_prod_conformance_test.clj.
-- Scripts follow Lean.Elab.Tactic.Induction.evalInductionCore/evalCasesCore,
-- Simp.evalSimp and Decide.evalDecideCore in src/Lean/Elab/Tactic/.
set_option linter.unusedSimpArgs false
def first : List Nat → Option Nat
  | [] => none
  | h :: _ => some h
def find (p : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | h :: t => if p h then some h else find p t
def lookup (k : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | h :: t => if Nat.beq k h.1 then some h.2 else lookup k t
def unpack (o : Option Nat) : Nat
  := match o with | none => 0 | some x => x
def swap (p : Nat × Nat) : Nat × Nat := (p.2, p.1)
def unzip : List (Nat × Nat) → List Nat × List Nat
  | [] => ([], [])
  | h :: t => (h.1 :: (unzip t).1, h.2 :: (unzip t).2)
def partition (p : Nat → Bool) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | h :: t => if p h then (h :: (partition p t).1, (partition p t).2)
                       else ((partition p t).1, h :: (partition p t).2)

theorem o01_first_nil  : first [] = none := by
  rfl

theorem o02_first_cons (x : Nat) (xs : List Nat) : first (x :: xs) = some x := by
  simp [first]

theorem o03_find_false (xs : List Nat) : find (fun _ => false) xs = none := by
  induction xs <;> simp [find, *]

theorem o04_find_true (xs : List Nat) : find (fun _ => true) xs = first xs := by
  cases xs <;> simp [find, first]

theorem o05_find_hit (p : Nat → Bool) (x : Nat) (xs : List Nat) (h : p x = true) : find p (x :: xs) = some x := by
  simp [find, h]

theorem o06_find_match (p : Nat → Bool) (xs : List Nat) : unpack (find p xs) = (match find p xs with | none => 0 | some x => x) := by
  cases h : find p xs <;> simp [unpack]

theorem o07_map_id (xs : List Nat) : Option.map (fun x => x) (first xs) = first xs := by
  cases h : first xs <;> simp [Option.map]

theorem o08_lookup_nil (k : Nat) : lookup k [] = none := by
  rfl

theorem o09_lookup_hit (k v : Nat) (xs : List (Nat × Nat)) : lookup k ((k,v) :: xs) = some v := by
  simp [lookup]

theorem o10_swap_twice (p : Nat × Nat) : swap (swap p) = p := by
  obtain ⟨a, b⟩ := p
  rfl

theorem o11_swap_fields (p : Nat × Nat) : (swap p).1 + (swap p).2 = p.1 + p.2 := by
  rcases p with ⟨a, b⟩
  simp [swap, Nat.add_comm]

theorem o12_unzip_nil  : unzip [] = ([], []) := by
  rfl

theorem o13_unzip_cons (a b : Nat) (xs : List (Nat × Nat)) : (unzip ((a,b) :: xs)).1 = a :: (unzip xs).1 := by
  simp [unzip]

theorem o14_partition_false (xs : List Nat) : (partition (fun _ => false) xs).1 = [] := by
  induction xs <;> simp [partition, *]

theorem o15_partition_true (xs : List Nat) : (partition (fun _ => true) xs).1 = xs := by
  induction xs <;> simp [partition, *]
