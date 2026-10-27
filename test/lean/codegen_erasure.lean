def propRuntimeProbe (p : Prop) : Prop := p ∧ p
example (p : Prop) : propRuntimeProbe p = (p ∧ p) := rfl
example (p : Prop) (h : propRuntimeProbe p) : p := h.left

def ignoreProposition (_ : Prop) (n : Nat) : Nat := n + 1
def passProposition (n : Nat) : Nat := ignoreProposition (propRuntimeProbe True) n
def runtimeType : Type := Nat
def ignoreType (_ : Type) (n : Nat) : Nat := n + 2
def passType (n : Nat) : Nat := ignoreType runtimeType n
def ignoreProof (p : Prop) (_ : p) (n : Nat) : Nat := n
def passProof (n : Nat) : Nat := ignoreProof True True.intro n
example : passProposition 3 = 4 := rfl
example : passType 3 = 5 := rfl
example : passProof 3 = 3 := rfl

def ignorePredicate (_ : Nat → Prop) (n : Nat) : Nat := n + 3
def passPredicate (n : Nat) : Nat :=
  let p := fun x : Nat => x = x
  ignorePredicate p n
example : passPredicate 3 = 6 := rfl

def letIgnoreType (_ : Type) (n : Nat) : Nat := n
def letTypeAlias : Nat :=
  let T : Type 1 := Type
  let f : Nat → T := fun _ => Nat
  letIgnoreType (f 0) 7
def nestedLetTypeAlias : Nat :=
  let T : Type 1 := Type
  let U : Type 1 := T
  let f : Nat → U := fun _ => Nat
  let g : Nat → U := f
  letIgnoreType (g 0) 7
example : letTypeAlias = 7 := rfl
example : nestedLetTypeAlias = 7 := rfl
