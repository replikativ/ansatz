-- Function-valued definitions and application shapes used by the runtime differential tests.
def roundProbe : Nat → Nat → Bool
  | 0 => fun _ => true
  | n + 1 => fun x => roundProbe n x
def badCallProbe (n x : Nat) : Bool := (roundProbe n) x
example : badCallProbe 2 3 = true := rfl
#guard badCallProbe 2 3 == true

def resultLet (n x : Nat) : Bool := let f := roundProbe n; f x
def resultFlat (n x y : Nat) : Nat := n + (x + y)
def resultMulti (n x : Nat) : Nat → Nat := fun y => n + (x + y)
def resultRecursive (n x : Nat) : Nat → Nat :=
  match n with
  | 0 => fun y => x + y
  | k + 1 => fun y => 1 + resultRecursive k x y
def resultEta (n : Nat) : Nat → Nat := fun x => resultFlat n x 3
def resultPartial (n : Nat) : Nat → Nat := resultFlat n 2
def resultNested (n : Nat) : Nat → Nat → Nat := fun x => fun y => n + (x + y)
def resultValue : Nat → Nat → Nat → Nat := resultFlat
def resultLocal (n x y : Nat) : Nat := let f := resultMulti n; (f x) y

example : resultLet 2 3 = true := rfl
example : resultMulti 2 3 5 = 10 := rfl
example : (resultMulti 2 3) 5 = 10 := rfl
example : resultRecursive 2 3 5 = 10 := rfl
example : (let f := resultMulti; f 2 3 5) = 10 := rfl
example : resultEta 2 5 = 10 := rfl
example : resultPartial 2 5 = 9 := rfl
example : resultNested 2 3 5 = 10 := rfl
example : resultValue 2 3 5 = 10 := rfl
example : resultLocal 2 3 5 = 10 := rfl
