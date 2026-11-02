import Init

-- Public Init roots: Bool, Option and List lemmas, and Nat.zero_ne_add_one.
example : (false : Bool) ≠ true := Bool.false_ne_true
example (b : Bool) : b = true ∨ b = false := Bool.eq_false_or_eq_true b
example (b : Bool) : b = false ↔ b ≠ true := Bool.eq_false_iff
example (b : Bool) : b ≠ false ↔ b = true := Bool.ne_false_iff
example (x : Nat) : (some x : Option Nat) ≠ none := Option.some_ne_none x
example (x : Nat) (xs : List Nat) : x :: xs ≠ [] := List.cons_ne_nil x xs
example (n : Nat) : 0 ≠ n + 1 := Nat.zero_ne_add_one n
example (f g : Nat → Nat) (xs : List Nat) : (xs.map f).map g = xs.map (fun x => g (f x)) := List.map_map
example (f : Nat → Nat) (x : Nat) : (some x).map f = some (f x) := Option.map_some x f
example (f : Nat → Nat) : (none : Option Nat).map f = none := Option.map_none f
