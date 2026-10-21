macro "hostedNat" x:term : term => `($x)
macro "hostedString" x:term : term => `($x)
namespace ReconstructionMacroA
def nat (x : Nat) : Nat := hostedNat x
def text (x : String) : String := hostedString x
end ReconstructionMacroA
