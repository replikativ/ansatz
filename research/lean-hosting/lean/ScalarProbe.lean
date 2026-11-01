import Init

namespace ScalarProbe
structure Packet where
  label : Nat
  word : USize
  small : UInt8
  medium : UInt32
  wide : UInt64

@[noinline] def makePacket (label : Nat) (word : USize) (small : UInt8) (medium : UInt32) (wide : UInt64) : Packet :=
  ⟨label, word, small, medium, wide⟩
@[noinline] def readWord (p : Packet) : USize := p.word
@[noinline] def readSmall (p : Packet) : UInt8 := p.small
@[noinline] def readMedium (p : Packet) : UInt32 := p.medium
@[noinline] def readWide (p : Packet) : UInt64 := p.wide
@[noinline] def replaceSmall (p : Packet) (value : UInt8) : Packet := { p with small := value }
@[noinline] def identity8 (x : UInt8) : UInt8 := x
@[noinline] def identity16 (x : UInt16) : UInt16 := x
@[noinline] def identity32 (x : UInt32) : UInt32 := x
@[noinline] def identity64 (x : UInt64) : UInt64 := x
@[noinline] def identitySize (x : USize) : USize := x
@[noinline] def apply64 (f : UInt64 → UInt64) (x : UInt64) : UInt64 := f x

def main : IO Unit := do
  let p := makePacket 7 4294967297 255 4294967295 18446744073709551615
  IO.println s!"{readWord p},{readSmall p},{readMedium p},{readWide p}"
  let q := replaceSmall p 3
  IO.println s!"{readSmall p},{readSmall q},{readMedium q},{readWide q}"
  IO.println s!"{apply64 identity64 18446744073709551615}"
end ScalarProbe

def main : IO Unit := ScalarProbe.main
