macro "hostedNat" x:term : term => `(Nat.succ $x)
macro "hostedString" x:term : term => `(String.append $x $x)
namespace ReconstructionMacroA
def nat (x : Nat) : Nat := hostedNat x
def text (x : String) : String := hostedString x
end ReconstructionMacroA
