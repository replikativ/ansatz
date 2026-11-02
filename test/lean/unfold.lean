import Lean

-- Lean counterpart of test/ansatz/tactic/unfold_test.clj (Lean 4.33.1, Init only).
-- `unfold f` delta-expands a non-recursive `f` and leaves other definitions folded.

structure UnfoldSt where
  hs : List Nat
  es : List Nat

def unfoldHcov : List Nat → List Nat → Bool
  | [], _ => true
  | h :: t, es => (h == 0) && unfoldHcov t es

def unfoldWrap (s : UnfoldSt) : Bool := unfoldHcov s.hs s.es

theorem unfoldWrap_of_hcov (f : UnfoldSt → UnfoldSt) (s : UnfoldSt)
    (h : unfoldHcov (f s).hs (f s).es = true) : unfoldWrap (f s) = true := by
  unfold unfoldWrap
  rw [h]

theorem unfoldWrap_exact (xs ys : List Nat) (h : unfoldHcov xs ys = true) :
    unfoldWrap ⟨xs, ys⟩ = true := by
  unfold unfoldWrap
  exact h

def unfoldTwice (n : Nat) : Nat := n + n

theorem unfoldTwice_forall : ∀ n : Nat, unfoldTwice n = n + n := by
  unfold unfoldTwice
  intro n
  rfl

-- unfolding a constant that does not occur fails
example (n : Nat) : n = n := by
  fail_if_success unfold unfoldTwice
  rfl

-- dsimp reduces a matcher whose selected alternative binds a constructor field
inductive UnfoldOut where
  | val
  | stuck (n : Nat)

structure UnfoldStore where
  w : Nat
  l : List Nat

def unfoldAmount : Nat → Option Nat
  | 0 => none
  | k + 1 => some k

def unfoldSpendH (_ : UnfoldStore) (n : Nat) : UnfoldOut := .stuck n

def unfoldSpendN (s : UnfoldStore) (x : Nat) : UnfoldOut :=
  match unfoldAmount x with
  | none => .stuck 0
  | some n => match s with | ⟨_, _⟩ => unfoldSpendH s n

theorem unfoldSpendN_nv (s : UnfoldStore) (x : Nat) : unfoldSpendN s x ≠ .val := by
  cases s
  unfold unfoldSpendN
  cases qa : unfoldAmount x
  all_goals dsimp only
  · intro h; cases h
  · intro h; cases h

-- Inspect the target immediately; rfl alone would not test the transformation.
example (s : UnfoldSt) : unfoldWrap s = unfoldHcov s.hs s.es := by
  unfold unfoldWrap
  guard_target =ₛ unfoldHcov s.hs s.es = unfoldHcov s.hs s.es
  rfl

example : ∀ n, unfoldTwice n = n + n := by
  unfold unfoldTwice
  guard_target =ₛ ∀ n : Nat, n + n = n + n
  intro n; rfl

def deltaLet : Nat → Nat := let y := 7; fun _ => y
example : deltaLet 0 = 7 := by
  unfold deltaLet
  guard_target =ₛ 7 = 7
  rfl

def deltaUniverse.{u} : Type u := PUnit.{u+1}
example : deltaUniverse.{1} = PUnit.{2} := by
  unfold deltaUniverse
  guard_target =ₛ PUnit.{2} = PUnit.{2}
  rfl

def matcherField (x : Option Nat) : Nat := match x with
  | none => 13
  | some n => n
example (n m : Nat) (h : n = m) : matcherField (some n) = m := by
  unfold matcherField
  dsimp only
  guard_target =ₛ n = m
  exact h

def hiddenBool : Bool := true
def matcherBool (x : Bool) : Nat := match x with
  | false => 13
  | true => 21
example : matcherBool hiddenBool = 21 := by
  unfold matcherBool
  fail_if_success dsimp only
  guard_target =ₛ (match hiddenBool with | false => 13 | true => 21) = 21
  rfl

-- Local let declarations cannot alias the fresh locals used by reduceMatcher?.
example (g : Unit → Nat) (n : Nat) (h : 13 = n) : matcherBool false = n := by
  let f : Unit → Nat := g
  unfold matcherBool
  dsimp only
  guard_target =ₛ 13 = n
  exact h

namespace Innocent
 def brecOn (n : Nat) := n
end Innocent
def reviewWrap (n : Nat) := Innocent.brecOn n
example : ∀ n, reviewWrap n = Innocent.brecOn n := by
  unfold reviewWrap
  guard_target =ₛ ∀ n, Innocent.brecOn n = Innocent.brecOn n
  intro n; rfl

namespace UnfoldOrder
structure Store where
  wallet : Nat
  spent : Nat

def takeN (s : Store) (n : Nat) : Nat :=
  match s with
  | ⟨w, _⟩ => match Nat.ble n w with
    | true => 21
    | false => 13

-- Splitting before dsimp does not find the test hidden under the matcher binder.
example (s : Store) (n : Nat) : takeN s n = 13 ∨ takeN s n = 21 := by
  cases s with
  | mk wallet spent =>
    unfold takeN
    cases qb : Nat.ble n wallet
    all_goals dsimp only
    · fail_if_success exact Or.inl rfl
      simp only [qb]
      exact Or.inl True.intro
    · simp only [qb]
      exact Or.inr True.intro

-- Expose the test first, then split it.
example (s : Store) (n : Nat) : takeN s n = 13 ∨ takeN s n = 21 := by
  cases s with
  | mk wallet spent =>
    unfold takeN
    dsimp only
    cases qb : Nat.ble n wallet
    all_goals dsimp only
    · exact Or.inl rfl
    · exact Or.inr rfl

end UnfoldOrder

-- betaRev consumes every supplied argument.
def deltaMany
    (_x0 _x1 _x2 _x3 _x4 _x5 _x6 _x7 _x8 _x9 : Nat)
    (_x10 _x11 _x12 _x13 _x14 _x15 _x16 _x17 _x18 _x19 : Nat)
    (_x20 _x21 _x22 _x23 _x24 _x25 _x26 _x27 _x28 _x29 : Nat)
    (_x30 _x31 _x32 _x33 _x34 _x35 _x36 _x37 _x38 _x39 : Nat)
    (_x40 _x41 _x42 _x43 _x44 _x45 _x46 _x47 _x48 _x49 : Nat)
    (_x50 _x51 _x52 _x53 _x54 _x55 _x56 _x57 _x58 _x59 : Nat)
    (_x60 _x61 _x62 _x63 _x64 _x65 _x66 _x67 _x68 _x69 : Nat)
    (_x70 _x71 _x72 _x73 _x74 _x75 _x76 _x77 _x78 _x79 : Nat)
    (_x80 _x81 _x82 _x83 _x84 _x85 _x86 _x87 _x88 _x89 : Nat)
    (_x90 _x91 _x92 _x93 _x94 _x95 _x96 _x97 _x98 _x99 : Nat)
    (_x100 _x101 _x102 _x103 _x104 _x105 _x106 _x107 _x108 _x109 : Nat)
    (_x110 _x111 _x112 _x113 _x114 _x115 _x116 _x117 _x118 _x119 : Nat)
    (_x120 _x121 _x122 _x123 _x124 _x125 _x126 _x127 _x128 _x129 : Nat)
    (_x130 _x131 _x132 _x133 _x134 _x135 _x136 _x137 _x138 _x139 : Nat)
    : Nat := 7
example : deltaMany 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = 7 := by
  unfold deltaMany
  guard_target =ₛ 7 = 7
  rfl

-- An existing eq_def is used even for a nonrecursive definition. Its proof
-- must be transported; delta expansion alone cannot produce this target.
def equationConstant : Nat := 0
run_meta do
  let type ← Lean.Meta.mkEq (Lean.mkConst ``equationConstant) (Lean.mkNatLit 1)
  Lean.addDecl (.axiomDecl { name := `equationConstant.eq_def, levelParams := [], type, isUnsafe := false })
example : equationConstant = 1 := by
  unfold equationConstant
  guard_target =ₛ 1 = 1
  rfl
example : ∀ _ : Nat, equationConstant = 1 := by
  unfold equationConstant
  guard_target =ₛ ∀ _ : Nat, 1 = 1
  intro n; rfl

def unfoldType : Type := Nat
run_meta do
  let type ← Lean.Meta.mkEq (Lean.mkConst ``unfoldType) (Lean.mkConst ``Bool)
  Lean.addDecl (.axiomDecl { name := `unfoldType.eq_def, levelParams := [], type, isUnsafe := false })
example : (Nat → unfoldType) = (Nat → Bool) := by
  unfold unfoldType
  guard_target =ₛ (Nat → Bool) = (Nat → Bool)
  rfl

noncomputable def nestedDite.match_1 : (Bool → Type) → Bool → (Unit → Nat) → (Unit → Nat) → Nat :=
  @dite _ True (Decidable.isTrue True.intro) (fun _ => fun _ b f t => @Bool.rec (fun _ => Nat) (f ()) (t ()) b)
            (fun _ => fun _ b f t => @Bool.rec (fun _ => Nat) (f ()) (t ()) b)
open Lean Meta in
run_meta do
  Match.addMatcherInfo ``nestedDite.match_1 {
    numParams := 0, numDiscrs := 1, uElimPos? := none,
    altInfos := #[{ numFields := 0, numOverlaps := 0, hasUnitThunk := true },
                 { numFields := 0, numOverlaps := 0, hasUnitThunk := true }],
    discrInfos := #[{}], overlaps := {} }
  let alt (v : Nat) := mkLambda `u .default (mkConst ``Unit) (mkNatLit v)
  let expr := mkAppN (mkConst ``nestedDite.match_1) #[mkLambda `b .default (mkConst ``Bool) (mkConst ``Nat), mkConst ``Bool.false, alt 13, alt 21]
  discard <| inferType expr
  let .reduced r ← withReducible <| reduceMatcher? expr | throwError "matcher stuck"
  unless r == mkNatLit 13 do throwError "unexpected result {r}"

-- Non-propositional dependent Pi types admit only definitional rewrites.
def unfoldFamily (_ : Nat) : Type := Nat
run_meta do
  let type := Lean.mkForall `n .default (Lean.mkConst ``Nat)
    (← Lean.Meta.mkEq (Lean.mkApp (Lean.mkConst ``unfoldFamily) (Lean.mkBVar 0)) (Lean.mkConst ``Bool))
  Lean.addDecl (.axiomDecl { name := `unfoldFamily.eq_def, levelParams := [], type, isUnsafe := false })
example : (∀ n, unfoldFamily n) = (Nat → Nat) := by
  fail_if_success unfold unfoldFamily
  rfl
