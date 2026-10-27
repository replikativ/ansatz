-- Init-only grind yardstick for ansatz.grind-conformance-test.
-- Core cases adapted from lean4/tests/lean/run/grind_t1.lean and grind_split.lean;
-- list/model cases adapted from list_conformance.lean and memory_model_probe.lean.
-- No admissions, extra imports, or helper proofs. Names and order match the Clojure suite.

namespace GrindConformance

def app : List Nat → List Nat → List Nat | [], ys => ys | h::t, ys => h::app t ys

def len : List Nat → Nat | [] => 0 | _::t => len t + 1

def map (f : Nat → Nat) : List Nat → List Nat | [] => [] | h::t => f h :: map f t

def filter (p : Nat → Bool) : List Nat → List Nat | [] => [] | h::t => if p h then h::filter p t else filter p t

structure Own where
  ent : Nat
  scope : Nat

def memq (x : Nat) : List Nat → Bool | [] => false | h::t => if Nat.beq x h then true else memq x t

def dropNat (x : Nat) : List Nat → List Nat | [] => [] | h::t => if Nat.beq h x then dropNat x t else h::dropNat x t

def ownersOpen : List Own → List Nat → Bool | [], _ => true | o::t, op => if memq o.scope op then ownersOpen t op else false

def dropOwned (sc : Nat) : List Own → List Own | [] => [] | o::t => if Nat.beq o.scope sc then dropOwned sc t else o::dropOwned sc t

theorem g01_trans (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  grind

theorem g02_congr (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  grind

theorem g03_nested (f g : Nat → Nat) (a b c : Nat) (h₁ : a = c) (h₂ : b = c) : f (g a) = f (g b) := by
  grind

theorem g04_list_clash (a b : List Nat) : a = [] → b = [2] → a = b → False := by
  grind

theorem g05_bool_clash (a b : Bool) : a = true → b = false → a = b → False := by
  grind

theorem g06_inject_head (a c : Nat) (b d : List Nat) (h : a::b = c::d) : a = c := by
  grind

theorem g07_inject_tail (a c : Nat) (b d : List Nat) (h : a::b = c::d) : b = d := by
  grind

theorem g08_and_comm (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by
  grind

theorem g09_or_resolve (p q : Prop) (h₁ : p ∨ q) (h₂ : ¬p) : q := by
  grind

theorem g10_split_unsat (p q : Prop) : p ∨ q → p ∨ ¬q → ¬p ∨ q → ¬p ∨ ¬q → False := by
  grind

theorem g11_modus (p q : Prop) (h₁ : p → q) (h₂ : p) : q := by
  grind

theorem g12_ematch (f : Nat → Nat) (h : ∀ x, f x = x) (a : Nat) : f (f a) = a := by
  grind

theorem g13_forward (p q : Nat → Prop) (h : ∀ x, p x → q x) (a : Nat) (ha : p a) : q a := by
  grind

theorem g14_if_true (b : Bool) (x y : Nat) (h : b = true) : (if b then x else y) = x := by
  grind

theorem g15_if_false (b : Bool) (x y : Nat) (h : b = false) : (if b then x else y) = y := by
  grind

theorem g16_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  grind [Nat.beq_eq]

theorem g17_linear (a b : Nat) (h : a < b) : ¬ b < a := by
  grind

theorem g18_ring (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
  grind

theorem g19_app_nil (xs : List Nat) : app xs [] = xs := by
  induction xs <;> grind [app]

theorem g20_app_assoc (xs ys zs : List Nat) : app (app xs ys) zs = app xs (app ys zs) := by
  induction xs <;> grind [app]

theorem g21_len_app (xs ys : List Nat) : len (app xs ys) = len xs + len ys := by
  induction xs <;> grind [len, app]

theorem g22_len_map (f : Nat → Nat) (xs : List Nat) : len (map f xs) = len xs := by
  induction xs <;> grind [len, map]

theorem g23_map_app (f : Nat → Nat) (xs ys : List Nat) : map f (app xs ys) = app (map f xs) (map f ys) := by
  induction xs <;> grind [map, app]

theorem g24_map_id (xs : List Nat) : map (fun x => x) xs = xs := by
  induction xs <;> grind [map]

theorem g25_filter_app (p : Nat → Bool) (xs ys : List Nat) : filter p (app xs ys) = app (filter p xs) (filter p ys) := by
  induction xs <;> grind [filter, app]

theorem g26_filter_idem (p : Nat → Bool) (xs : List Nat) : filter p (filter p xs) = filter p xs := by
  induction xs <;> grind [filter]

theorem g27_filter_len (p : Nat → Bool) (xs : List Nat) : len (filter p xs) ≤ len xs := by
  induction xs <;> grind [filter, len]

theorem g28_memq_drop (x sc : Nat) (op : List Nat) : memq x op = true → Nat.beq x sc = false → memq x (dropNat sc op) = true := by
  induction op <;> grind [memq, dropNat, Nat.beq_eq]

theorem g29_owners_drop (sc : Nat) (op : List Nat) (os : List Own) : ownersOpen os op = true → ownersOpen (dropOwned sc os) (dropNat sc op) = true := by
  induction os <;> grind [ownersOpen, dropOwned, Nat.beq_eq, g28_memq_drop]

theorem g30_owners_hyp (sc : Nat) (op : List Nat) (os : List Own) (h : ownersOpen os op = true) : ownersOpen (dropOwned sc os) (dropNat sc op) = true := by
  induction os <;> grind [ownersOpen, dropOwned, Nat.beq_eq, g28_memq_drop]

end GrindConformance
