import NativeBuiltinWitnessFixtures

/- Independent semantic oracle. Imported defining-type products remain unchanged.
No type/layout schema, hand-written runtime objects or callable ABI is supplied. -/
open NativeNominalFixtures NativeBuiltinWitnessFixtures
namespace NativeDatatypeOracle

def makeAST (seed : Nat) : AST :=
  .binary .multiply (.sequence [.literal seed, .binary .add (.literal 3) (.literal 5)])
    (.packed #[.literal 11, .literal 23])

/- Bounded semantic reader: 16 levels suffice for this finite fixture. A fuel
exhaustion sentinel is explicit so deeper host inputs cannot silently match. -/
def readASTFuel : Nat → AST → Nat
  | 0, _ => 999999
  | _fuel + 1, .literal n => 7 + n
  | fuel + 1, .binary op left right =>
      (match op with | .add => 100 | .multiply => 200) +
        3 * readASTFuel fuel left + 5 * readASTFuel fuel right
  | fuel + 1, .sequence children =>
      300 + (children.map (readASTFuel fuel)).foldl (· + ·) 0
  | fuel + 1, .packed children =>
      400 + (children.map (readASTFuel fuel)).foldl (· + ·) 0

def readAST (value : AST) : Nat := readASTFuel 16 value

def makeMixed (seed : Nat) : Mixed := {
  label := "lean→JVM λ"
  count := UInt32.ofNat (0x89abcdef + seed)
  checksum := 0xfedcba9876543210
  index := 0x01020304050607
  weight := Float32.ofBits 0x80000000
  measure := Float.ofBits 0x7ff8000000000042
  enabled := true
  character := 'λ'
  trivial := ()
  boxed := ⟨0x76543210⟩
  product := (⟨0x12345678⟩, ())
  items := #[⟨7⟩, ⟨UInt32.ofNat seed⟩]
  payload := ByteArray.mk #[0, 127, 255]
  order := .gt
}

def readMixed (value : Mixed) : List Nat :=
  [value.label.utf8ByteSize, value.count.toNat, value.checksum.toNat, value.index.toNat,
   value.weight.toBits.toNat, value.measure.toBits.toNat,
   (if value.enabled then 1 else 0), value.character.toNat,
   (match value.trivial with | () => 77), value.boxed.value.toNat,
   value.product.1.value.toNat, (match value.product.2 with | () => 91),
   value.items.size, (value.items.getD 0 ⟨0⟩).value.toNat, (value.items.getD 1 ⟨0⟩).value.toNat,
   value.payload.size, value.payload[0]!.toNat, value.payload[1]!.toNat, value.payload[2]!.toNat,
   (match value.order with | .lt => 41 | .eq => 43 | .gt => 47)]

def makeScalars (seed : Nat) : Scalars :=
  ⟨0xab, 0xfedcba9876543210, USize.ofNat seed, Float32.ofBits 0x3fc00000⟩

def readScalars (value : Scalars) : List Nat :=
  [value.narrow.toNat, value.wide.toNat, value.index.toNat, value.weight.toBits.toNat]

def makeContainers (seed : Nat) : Containers := {
  maybe := some (UInt32.ofNat seed)
  choice := .inl 0xab
  outcome := .error "fail-β"
  numbers := [3, seed, 11]
  pair := (101 + seed, ())
}

def readContainers (value : Containers) : List Nat :=
  [(match value.maybe with | none => 17 | some n => 1000 + n.toNat),
   (match value.choice with | .inl n => 2000 + n.toNat | .inr s => 3000 + s.utf8ByteSize),
   (match value.outcome with | .error s => 4000 + s.utf8ByteSize | .ok n => 5000 + n),
   value.numbers.length, value.numbers.foldl (fun acc n => acc * 31 + n) 0,
   value.pair.1, (match value.pair.2 with | () => 113)]

def readOptionUnit : Option Unit → Nat
  | none => 17
  | some () => 29

end NativeDatatypeOracle

/- JSON consists entirely of actual Lean observations. Float payloads are read
with the real toBits primitives, not reproduced from source literals. -/
def main : IO Unit := do
  let seed := 23
  let ast := NativeDatatypeOracle.readAST (NativeDatatypeOracle.makeAST seed)
  let mixed := NativeDatatypeOracle.readMixed (NativeDatatypeOracle.makeMixed seed)
  let scalars := NativeDatatypeOracle.readScalars (NativeDatatypeOracle.makeScalars seed)
  let containers := NativeDatatypeOracle.readContainers (NativeDatatypeOracle.makeContainers seed)
  let units := [NativeDatatypeOracle.readOptionUnit none, NativeDatatypeOracle.readOptionUnit (some ())]
  IO.println <| "{\"schema\":\"lean-jvm-native-datatype-oracle/1\",\"seed\":" ++ toString seed ++
    ",\"ast\":" ++ toString ast ++ ",\"mixed\":" ++ toString mixed ++
    ",\"scalars\":" ++ toString scalars ++ ",\"containers\":" ++ toString containers ++
    ",\"optionUnit\":" ++ toString units ++ "}"
