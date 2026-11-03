import NativeNominalFixtures

/- Ordinary declarations only; the producer discovers each closed type. -/
namespace NativeBuiltinWitnessFixtures

structure Containers where
  maybe : Option UInt32
  choice : Sum UInt8 String
  outcome : Except String Nat
  numbers : List Nat
  pair : Prod Nat Unit

end NativeBuiltinWitnessFixtures
