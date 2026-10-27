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

-- Nonrecursive values need no well-founded fixpoint, regardless of annotation
-- at the Ansatz surface. Partial definitions stay opaque in the kernel.
def valueZero : Nat → Nat := fun x => x + 1
def valueOne (n : Nat) : Nat → Nat := fun x => n + x
def valueTwo (n b : Nat) : Nat → Nat := fun x => n + (b + x)
partial def partialZero : Nat → Nat := fun x => x + 1
partial def partialOne (n : Nat) : Nat → Nat := fun x => n + x
partial def partialTwo (n b : Nat) : Nat → Nat := fun x => n + (b + x)
partial def partialRecZero : Nat → Nat := fun x =>
  if x ≤ 0 then 1 else 1 + partialRecZero (x - 1)
partial def partialRecOne (n : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => x else fun x => partialRecOne (n - 1) (x + 1)
partial def partialRecTwo (n b : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => b + x else fun x => partialRecTwo (n - 1) b (x + 1)
def wfRecOne (n : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => x else fun x => wfRecOne (n - 1) (x + 1)
termination_by n
decreasing_by omega
def wfRecTwo (n b : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => b + x else fun x => wfRecTwo (n - 1) b (x + 1)
termination_by n
decreasing_by omega

def recOracle (n b : Nat) : Nat → Nat :=
  match n with
  | 0 => fun x => b + x
  | k + 1 => fun x => 1 + recOracle k b x
def wfRecZero : Nat → Nat := fun x => recOracle x 1 0
example : valueZero 4 = 5 := rfl
example : valueOne 3 4 = 7 := rfl
example : valueTwo 3 2 4 = 9 := rfl
example : wfRecZero 4 = 5 := rfl
/-- info: true -/
#guard_msgs in
#eval partialZero 4 == valueZero 4 && partialOne 3 4 == valueOne 3 4 &&
      partialTwo 3 2 4 == valueTwo 3 2 4 && partialRecZero 4 == recOracle 4 1 0 &&
      partialRecOne 3 4 == recOracle 3 0 4 && partialRecTwo 3 2 4 == recOracle 3 2 4 &&
      wfRecOne 3 4 == recOracle 3 0 4 && wfRecTwo 3 2 4 == recOracle 3 2 4

def wfFuel (n : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => x
  else fun x => let y := x + 1; wfFuel (n - 1) y
termination_by n
decreasing_by omega
/-- info: true -/
#guard_msgs in
#eval wfFuel 0 5 == 5 && wfFuel 4 5 == 9

partial def polyResult {S : Type} (n : S) : Nat → S := fun _ => n
def implicitResult {_S : Type} (n : Nat) : Nat → Nat := fun x => n + x
def instanceResult [Inhabited Nat] (n : Nat) : Nat → Nat := fun x => n + x
def implicitWf {S : Type} (n : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => x else fun x => 1 + @implicitWf S (n - 1) x
termination_by n
decreasing_by omega
def instanceWf [inst : Inhabited Nat] (n : Nat) : Nat → Nat :=
  if n ≤ 0 then fun x => x else fun x => 1 + @instanceWf inst (n - 1) x
termination_by n
decreasing_by omega
def fallbackScalar (n : Nat) : Nat :=
  if n ≤ 0 then 0 else 1 + fallbackScalar (n - 1)
termination_by n
decreasing_by omega
/-- info: true -/
#guard_msgs in
#eval polyResult 7 3 == 7 && @implicitResult Nat 4 3 == 7 &&
      @instanceResult ⟨0⟩ 4 3 == 7 && @implicitWf Nat 4 3 == 7 &&
      @instanceWf ⟨0⟩ 4 3 == 7 && fallbackScalar 4 == 4

-- Csimp replacements may use a different declared parameter telescope.
def originalFlat (n x : Nat) : Nat := n + x
def replacementResult (n : Nat) : Nat → Nat := fun x => n + x
@[csimp] theorem replaceOriginal : originalFlat = replacementResult := rfl
def originalResult (n : Nat) : Nat → Nat := fun x => n + x
def replacementFlat (n x : Nat) : Nat := n + x
@[csimp] theorem replaceResult : originalResult = replacementFlat := rfl
example : (let f := originalFlat; f 2 3) = 5 := rfl
example : (let f := originalResult; f 2 3) = 5 := rfl
/-- info: true -/
#guard_msgs in
#eval (let f := originalFlat; f 2 3) == 5 && (let f := originalResult; f 2 3) == 5
