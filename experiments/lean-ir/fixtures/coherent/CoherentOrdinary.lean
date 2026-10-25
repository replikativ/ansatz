namespace CoherentOrdinary
inductive Bit where | zero | one
def bit (x : Bit) : Nat := match x with | .zero => 0 | .one => 1
def answer (n : Nat) : Nat := n + bit .one
def nat (x : Nat) : Nat := x
def text (x : String) : String := x
end CoherentOrdinary
