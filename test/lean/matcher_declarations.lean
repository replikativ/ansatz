import Lean

-- Keep proof-valued functions as definitions to exercise matcher generation.
set_option linter.defProp false

namespace MatcherDeclarations

inductive Enum where
  | red | green | blue

def enumValue (x : Enum) : Nat :=
  match x with
  | .red => 7
  | .green => 8
  | _ => 9

def nested (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | [x] => x
  | _ :: y :: _ => y

def literal (n : Nat) : Nat :=
  match n with
  | 0 => 10
  | 1 => 20
  | k => k + 2

def stringValue (s : String) : Nat :=
  match s with
  | "yes" => 1
  | "no" => 2
  | _ => 0

def multiple (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => 100
  | n + 1, 0 => n
  | n + 1, m + 1 => n + m

def overlap (n : Nat) : Nat :=
  match n with
  | Nat.succ Nat.zero => 10
  | Nat.succ k => k
  | Nat.zero => 20

def product (p : Nat × Nat) : Nat :=
  match p with
  | (x, y) => x + y

inductive Vec (a : Type) : Nat → Type where
  | nil : Vec a 0
  | cons (n : Nat) (x : a) (xs : Vec a n) : Vec a (Nat.succ n)

def vector (n : Nat) (v : Vec Nat n) : Nat :=
  match v with
  | .nil => 0
  | .cons _ x _ => x

def branches (b : Bool) (n : Nat) : Nat :=
  match b with
  | false => match n with
    | 0 => 5
    | Nat.succ k => k
  | true => match n with
    | 0 => 7
    | Nat.succ k => k + 1

def recursive (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ k => recursive k + 1

def impossible (x : Empty) : Nat := nomatch x

-- Each equality observes the selected branch or a local produced by its pattern.
example : enumValue .blue = 9 := rfl
example (x y : Nat) (ys : List Nat) : nested (x :: y :: ys) = y := rfl
example (x : Nat) : nested [x] = x := rfl
example : literal 0 = 10 := rfl
example : literal 5 = 7 := rfl
example : stringValue "yes" = 1 := rfl
example : stringValue "other" = 0 := rfl
example : multiple 0 3 = 100 := rfl
example : multiple 4 0 = 3 := rfl
example : multiple 4 3 = 5 := rfl
example : overlap 1 = 10 := rfl
example : overlap 4 = 3 := rfl
example : product (4, 9) = 13 := rfl
example : vector 1 (.cons 0 17 .nil) = 17 := rfl
example : branches false 4 = 3 := rfl
example : branches true 4 = 4 := rfl
example : recursive 7 = 7 := rfl

def dependentBool (b : Bool) (h : b = b) : b = b :=
  match b with
  | false => h
  | true => h

def dependentNat (n : Nat) (h : n = n) : n = n :=
  match n with
  | 0 => h
  | Nat.succ _ => h

def fixedVector (n : Nat) (v : Vec Nat (Nat.succ n)) : Nat :=
  match v with
  | .cons _ x _ => x

example : dependentBool false rfl = rfl := rfl
example : dependentBool true rfl = rfl := rfl
example : dependentNat 0 rfl = rfl := rfl
example : dependentNat 7 rfl = rfl := rfl
example : fixedVector 0 (.cons 0 17 .nil) = 17 := rfl
example : fixedVector 1 (.cons 1 23 (.cons 0 17 .nil)) = 23 := rfl

def dependentChain (b : Bool) (h : b = b) (p : h = h) : h = h :=
  match b with
  | false => p
  | true => p

def patternShadow (n : Nat) (h : n = n) : Nat :=
  match n with
  | 0 => 13
  | Nat.succ h => h

example : dependentChain false rfl rfl = rfl := rfl
example : patternShadow 7 rfl = 6 := rfl

def proofLets (b : Bool) (n : Nat) : Nat :=
  let x : Nat := match b with
    | false => n
    | true => n + 1
  let p : x = x := rfl
  let _q : p = p := rfl
  x

def proofReturn (b : Bool) (n : Nat) : n = n :=
  match b with
  | false => rfl
  | true => rfl

example : proofLets false 7 = 7 := rfl
example : proofLets true 7 = 8 := rfl
example : proofReturn false 7 = rfl := rfl
example : proofReturn true 7 = rfl := rfl

end MatcherDeclarations
