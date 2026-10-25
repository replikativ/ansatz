import CoherentA
namespace CoherentB
def add (x : Nat) : Nat := CoherentA.add x + 1
end CoherentB
