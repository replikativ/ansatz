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

@[instance_reducible] def explicitNumeralInstance (_α : Type) (n : Nat) : OfNat Nat n := ⟨n⟩
def explicitNumeral : Nat := @OfNat.ofNat Nat 2 (explicitNumeralInstance Nat 2)
example : explicitNumeral = 2 := rfl

-- Closed reductions used by the runtime/kernel inventory.
example : List.foldr (· + ·) 0 [1, 2, 3] = 6 := rfl
example : List.map (· + 1) [1, 2, 3] = [2, 3, 4] := rfl
example : List.filter (2 ≤ ·) [1, 2, 3] = [2, 3] := rfl
example : List.filterMap some [1, 2, 3] = [1, 2, 3] := rfl
example : List.flatMap (fun x => [x]) [1, 2, 3] = [1, 2, 3] := rfl
example : List.append [1, 2, 3] [1, 2, 3] = [1, 2, 3, 1, 2, 3] := rfl
example : List.reverse [1, 2, 3] = [3, 2, 1] := rfl
example : List.get?Internal [1, 2, 3] 1 = some 2 := rfl
example : List.head? [1, 2, 3] = some 1 := rfl
example : List.tail [1, 2, 3] = [2, 3] := rfl
example : List.zip [1, 2, 3] [1, 2, 3] = [(1, 1), (2, 2), (3, 3)] := rfl
example : List.zipWith (· + ·) [1, 2, 3] [1, 2, 3] = [2, 4, 6] := rfl
example : List.take 2 [1, 2, 3] = [1, 2] := rfl
example : List.drop 2 [1, 2, 3] = [3] := rfl
example : List.any [1, 2, 3] (· == 2) = true := rfl
example : List.all [1, 2, 3] (· ≤ 9) = true := rfl
example : List.find? (· == 2) [1, 2, 3] = some 2 := rfl
example : List.contains [1, 2, 3] 2 = true := rfl
example : List.elem 2 [1, 2, 3] = true := rfl
example : List.replicate 3 2 = [2, 2, 2] := rfl
example : List.range 3 = [0, 1, 2] := rfl
example : List.sum [1, 2, 3] = 6 := rfl
example : List.lookup 1 [(1, 7)] = some 7 := rfl

example : List.filterMap (fun x => if x == 2 then some x else none) [1, 2] = [2] := rfl
example : List.lookup 1 ([] : List (Nat × Nat)) = none := rfl
example : List.lookup 2 [(1, 7)] = none := rfl

@[instance_reducible] def runtimeNeverEqual : BEq Nat := ⟨fun _ _ => false⟩
example : @List.contains Nat runtimeNeverEqual [2] 2 = false := rfl

def runtimeStoredValue : Nat := 7
example : runtimeStoredValue = 7 := rfl

example : @Decidable.decide (2 = 2) (Nat.decEq 2 2) = true := rfl
example : @Decidable.decide (2 = 3) (Nat.decEq 2 3) = false := rfl
example : @Decidable.decide (2 ≤ 3) (Nat.decLe 2 3) = true := rfl
example : @Decidable.decide (3 ≤ 2) (Nat.decLe 3 2) = false := rfl
example : @Decidable.decide (2 < 3) (Nat.decLt 2 3) = true := rfl
example : @Decidable.decide (2 < 2) (Nat.decLt 2 2) = false := rfl

def runtimeImplicitOffset {n : Nat} (x : Nat) : Nat := n + x
example : @runtimeImplicitOffset 5 7 = 12 := rfl

def runtimeStoredFalse : Bool := false
example : runtimeStoredFalse = false := rfl
def runtimeStoredUnit : Unit := ()
example : runtimeStoredUnit = () := rfl

example : (let f := @Prod.mk Nat Nat; f 2 7) = (2, 7) := rfl
example : List.zip [1, 2] [7] = [(1, 7)] := rfl
example : (fun (f : (α : Type) → (β : Type) → α → β → α × β) => f Nat Nat 2 7)
            @Prod.mk = (2, 7) := rfl
-- Init/Prelude.lean: decEq/Decidable.decide, synthesized at the operand type.
def boolEquality (b : Bool) : Bool := (fun x : Bool => decide (x = true)) b
example : boolEquality true = true := rfl
example : boolEquality false = false := rfl
example : decide ((3 : Nat) = 3) = true := rfl
example : decide ((3 : Nat) = 4) = false := rfl
example : decide ((-3 : Int) = -3) = true := rfl
example : decide ((-3 : Int) = 3) = false := rfl
example : decide ("hello" = "hello") = true := rfl
example : decide ("hello" = "world") = false := rfl
inductive EqualityColor where
  | red | blue
  deriving DecidableEq
example : decide (EqualityColor.red = .red) = true := rfl
example : decide (EqualityColor.red = .blue) = false := rfl
example : decide ([true] = [true]) = true := rfl
example : decide ([true] = [false]) = false := rfl

structure EqualityToken where
  deriving DecidableEq
example : decide (EqualityToken.mk = EqualityToken.mk) = true := rfl
example : decide ("é" = "é") = true := rfl
example : decide ("" = "a") = false := rfl

example : ([] : List Nat).length = 0 := rfl
example : ([1, 2, 3] : List Nat).length = 3 := rfl
example : List.append ([1, 2] : List Nat) [3] = [1, 2, 3] := rfl
