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
