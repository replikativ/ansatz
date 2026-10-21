import ReconstructionMacroA
namespace ReconstructionMacroB
def nat (x : Nat) : Nat := hostedNat x
def text (x : String) : String := hostedString x
end ReconstructionMacroB
