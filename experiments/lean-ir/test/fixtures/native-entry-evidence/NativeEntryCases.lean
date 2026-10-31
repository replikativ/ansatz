namespace NativeEntryCases

abbrev NatArrow := Nat → Nat
def natStep (x : Nat) : Nat := x + 1
def aliasIdentity : NatArrow := fun x => x
def stringCase (x : String) : String := if x.isEmpty then "empty" else "full"
def action : IO Unit := IO.println "native entry evidence"
def «7» (x : Nat) : Nat := x

def polymorphic {α : Type u} (x : α) : α := x
unsafe def unsafeIdentity (x : Nat) : Nat := x
partial def partialLoop (x : Nat) : Nat := partialLoop x
axiom noBody : Nat → Nat
theorem proofOnly : True := True.intro

end NativeEntryCases
