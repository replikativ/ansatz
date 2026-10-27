import Init

def foldlRuntimeProbe (xs : List Nat) : Nat := xs.foldl (fun n x => n + x) 0
example : foldlRuntimeProbe [1, 2] = 3 := rfl
example : List.foldl (fun n x : Nat => n * 10 + x) 7 [1, 2, 3] = 7123 := rfl
example : List.foldl (fun n x : Nat => n * 10 + x) 7 [] = 7 := rfl

namespace RuntimeOrigin
def inc (n : Nat) : Nat := n + 1
def seed : Nat := 9
end RuntimeOrigin
namespace RuntimeCaller
def call (n : Nat) : Nat := RuntimeOrigin.inc n
def value (n : Nat) : Nat := let f := RuntimeOrigin.inc; f (n + RuntimeOrigin.seed)
example : call 4 = 5 := rfl
example : value 4 = 14 := rfl
end RuntimeCaller

def runtimeEtaSuccessor : Nat → Nat := Nat.succ
example : runtimeEtaSuccessor 7 = 8 := rfl

def runtimeGuard (n : Nat) : Nat := if n ≤ 0 then 0 else n - 1
example : runtimeGuard 0 = 0 := rfl
example : runtimeGuard 4 = 3 := rfl

def runtimeEquationBody (n : Nat) : Nat :=
  let _unused := @List.brecOn.{0, 0}
  n
example (_n : Nat) : runtimeEquationBody 0 = 0 := rfl
example (n : Nat) : runtimeEquationBody n = n := rfl

def runtimeSubtype (x : { n : Nat // 0 ≤ n }) : Nat := x.val + 1
example : runtimeSubtype ⟨3, Nat.zero_le 3⟩ = 4 := rfl

def explicitNumeralInstance (_α : Type) (n : Nat) : OfNat Nat n := ⟨n⟩
def explicitNumeral : Nat := @OfNat.ofNat Nat 2 (explicitNumeralInstance Nat 2)
example : explicitNumeral = 2 := rfl
