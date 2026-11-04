/-! Integer arithmetic oracle: every Int, Nat and fixed-width unsigned extern the
Lean JVM SDK admits for ordinary arithmetic, at edge values (Long, small-Int and
width boundaries, zero divisors, oversized shifts). Float32 results print as
exact IEEE bits. Every `row i r 0` for `i < tableCount 0` and `r < rowCount i 0`,
concatenated in order, must be byte-identical under native Lean and the JVM
engine; one row per call keeps each JVM call inside the per-call instruction
budget. Operands depend on the runtime `seed`, so the compiler cannot fold them. -/

def line (op : String) (args : List String) (r : String) : String :=
  op ++ " " ++ " ".intercalate args ++ " = " ++ r ++ "\n"

def pow2 (k : Nat) : Nat := 2 ^ k

def ints (s : Nat) : List Int :=
  let i (n : Nat) : Int := Int.ofNat (n + s)
  [-(i (pow2 100)), -(i (pow2 64)), -(i (pow2 63)) - 1, -(i (pow2 63)), -(i (pow2 62)),
   -(i (pow2 31)) - 1, -(i (pow2 31)), -(i (pow2 31)) + 1, -(i 7), -(i 3), -(i 1), i 0, i 1, i 2, i 3, i 7,
   i (pow2 31) - 1, i (pow2 31), i (pow2 62), i (pow2 63) - 1, i (pow2 63), i (pow2 64), i (pow2 100)]

def nats (s : Nat) : List Nat :=
  [0, 1, 2, 3, 12, 18, 255, 256, pow2 32, pow2 62, pow2 63 - 1, pow2 63, pow2 64 - 1, pow2 64,
   pow2 100, 3 * pow2 100, pow2 100 - 1].map (· + s)

def edges (bits : Nat) (s : Nat) : List Nat :=
  [0, 1, 2, 3, 7, bits - 1, bits, bits + 1, pow2 (bits - 1) - 1, pow2 (bits - 1),
   pow2 bits - 2, pow2 bits - 1].map (· + s)

/-- One operation's output, produced one operand row at a time. -/
structure Table where
  rows : Nat
  row : Nat → String

/-- Every ordered operand pair; row `r` fixes the left operand `xs[r]`. -/
@[specialize] def table2 {α : Type} (op : String) (xs : List α) (fmt : α → String)
    (f : α → α → String) : Table :=
  ⟨xs.length, fun r => match xs[r]? with
    | some a => xs.foldl (fun acc b => acc ++ line op [fmt a, fmt b] (f a b)) ""
    | none => ""⟩

@[specialize] def table1 {α : Type} (op : String) (xs : List α) (fmt : α → String)
    (f : α → String) : Table :=
  ⟨xs.length, fun r => match xs[r]? with
    | some a => line op [fmt a] (f a)
    | none => ""⟩

def intSections (s : Nat) : List Table :=
  let xs := ints s
  let sh : Int → String := toString
  [table2 "Int.mul" xs sh (fun a b => toString (a * b)),
   table2 "Int.tdiv" xs sh (fun a b => toString (Int.tdiv a b)),
   table2 "Int.tmod" xs sh (fun a b => toString (Int.tmod a b)),
   table2 "Int.ediv" xs sh (fun a b => toString (a / b)),
   table2 "Int.emod" xs sh (fun a b => toString (a % b)),
   table2 "Int.fdiv" xs sh (fun a b => toString (Int.fdiv a b)),
   table2 "Int.fmod" xs sh (fun a b => toString (Int.fmod a b)),
   table2 "Int.divExact" xs sh (fun a b => toString (Int.divExact (a * b) b (Int.dvd_mul_left a b))),
   table1 "Int.decNonneg" xs sh (fun a => toString (Int.decNonneg a).decide),
   table1 "Int.toNat" xs sh (fun a => toString a.toNat),
   table1 "Int.pow3" xs sh (fun a => toString (a ^ 3))]

def natSections (s : Nat) : List Table :=
  let xs := nats s
  let sh : Nat → String := toString
  [table2 "Nat.land" xs sh (fun a b => toString (a &&& b)),
   table2 "Nat.lor" xs sh (fun a b => toString (a ||| b)),
   table2 "Nat.xor" xs sh (fun a b => toString (a ^^^ b)),
   table2 "Nat.gcd" xs sh (fun a b => toString (Nat.gcd a b)),
   table2 "Nat.lcm" xs sh (fun a b => toString (Nat.lcm a b)),
   table2 "Nat.divExact" xs sh (fun a b => toString (Nat.divExact (a * b) b (Nat.dvd_mul_left b a))),
   table1 "Nat.pred" xs sh (fun a => toString a.pred),
   table1 "Nat.log2" xs sh (fun a => toString a.log2)]

/-- One width's full operation table; `ofNat`/`toNat` are that width's conversions. -/
@[specialize] def wordSections {α : Type} [Add α] [Sub α] [Mul α] [Div α] [Mod α] [AndOp α] [OrOp α]
    [XorOp α] [Complement α] [Neg α] [ShiftLeft α] [ShiftRight α] [DecidableEq α] [LT α] [LE α]
    [DecidableRel (α := α) (· < ·)] [DecidableRel (α := α) (· ≤ ·)]
    (name : String) (bits : Nat) (s : Nat) (ofNat : Nat → α) (toNat : α → Nat) (log2 : α → α)
    (convs : List (String × (α → String))) : List Table :=
  let xs := (edges bits s).map ofNat
  let sh : α → String := fun a => toString (toNat a)
  [table2 (name ++ ".add") xs sh (fun a b => sh (a + b)),
   table2 (name ++ ".sub") xs sh (fun a b => sh (a - b)),
   table2 (name ++ ".mul") xs sh (fun a b => sh (a * b)),
   table2 (name ++ ".div") xs sh (fun a b => sh (a / b)),
   table2 (name ++ ".mod") xs sh (fun a b => sh (a % b)),
   table2 (name ++ ".land") xs sh (fun a b => sh (a &&& b)),
   table2 (name ++ ".lor") xs sh (fun a b => sh (a ||| b)),
   table2 (name ++ ".xor") xs sh (fun a b => sh (a ^^^ b)),
   table2 (name ++ ".shiftLeft") xs sh (fun a b => sh (a <<< b)),
   table2 (name ++ ".shiftRight") xs sh (fun a b => sh (a >>> b)),
   table2 (name ++ ".decEq") xs sh (fun a b => toString (decide (a = b))),
   table2 (name ++ ".decLt") xs sh (fun a b => toString (decide (a < b))),
   table2 (name ++ ".decLe") xs sh (fun a b => toString (decide (a ≤ b))),
   table1 (name ++ ".complement") xs sh (fun a => sh (~~~a)),
   table1 (name ++ ".neg") xs sh (fun a => sh (-a)),
   table1 (name ++ ".log2") xs sh (fun a => sh (log2 a))] ++
  convs.map (fun (label, f) => table1 (name ++ "." ++ label) xs sh f)

def u8Sections (s : Nat) : List Table :=
  wordSections "UInt8" 8 s UInt8.ofNat UInt8.toNat UInt8.log2
    [("toUInt16", fun a => toString a.toUInt16), ("toUInt32", fun a => toString a.toUInt32),
     ("toUInt64", fun a => toString a.toUInt64), ("toUSize", fun a => toString a.toUSize),
     ("toBitVec", fun a => toString a.toBitVec.toNat), ("toFloat", fun a => toString a.toFloat),
     ("toFloat32", fun a => toString a.toFloat32.toBits)]

def u16Sections (s : Nat) : List Table :=
  wordSections "UInt16" 16 s UInt16.ofNat UInt16.toNat UInt16.log2
    [("toUInt8", fun a => toString a.toUInt8), ("toUInt32", fun a => toString a.toUInt32),
     ("toUInt64", fun a => toString a.toUInt64), ("toUSize", fun a => toString a.toUSize),
     ("toBitVec", fun a => toString a.toBitVec.toNat), ("toFloat", fun a => toString a.toFloat),
     ("toFloat32", fun a => toString a.toFloat32.toBits)]

def u32Sections (s : Nat) : List Table :=
  wordSections "UInt32" 32 s UInt32.ofNat UInt32.toNat UInt32.log2
    [("toUInt8", fun a => toString a.toUInt8), ("toUInt16", fun a => toString a.toUInt16),
     ("toUInt64", fun a => toString a.toUInt64), ("toUSize", fun a => toString a.toUSize),
     ("toFloat", fun a => toString a.toFloat), ("toFloat32", fun a => toString a.toFloat32.toBits)]

def u64Sections (s : Nat) : List Table :=
  wordSections "UInt64" 64 s UInt64.ofNat UInt64.toNat UInt64.log2
    [("toUInt8", fun a => toString a.toUInt8), ("toUInt16", fun a => toString a.toUInt16),
     ("toUInt32", fun a => toString a.toUInt32), ("toUSize", fun a => toString a.toUSize),
     ("toFloat", fun a => toString a.toFloat), ("toFloat32", fun a => toString a.toFloat32.toBits)]

def usizeSections (s : Nat) : List Table :=
  wordSections "USize" 64 s USize.ofNat USize.toNat USize.log2
    [("toUInt8", fun a => toString a.toUInt8), ("toUInt16", fun a => toString a.toUInt16),
     ("toUInt32", fun a => toString a.toUInt32), ("toUInt64", fun a => toString a.toUInt64),
     ("toFloat", fun a => toString a.toFloat), ("toFloat32", fun a => toString a.toFloat32.toBits)]

/-- Nat to word conversions (borrowed `ofNat`, owned `ofBitVec`) and Bool to word. -/
def conversionSections (s : Nat) : List Table :=
  let xs := nats s ++ [pow2 100 + 257 + s]
  let sh : Nat → String := toString
  [table1 "UInt8.ofNat" xs sh (fun n => toString (UInt8.ofNat n)),
   table1 "UInt16.ofNat" xs sh (fun n => toString (UInt16.ofNat n)),
   table1 "UInt32.ofNat" xs sh (fun n => toString (UInt32.ofNat n)),
   table1 "UInt64.ofNat" xs sh (fun n => toString (UInt64.ofNat n)),
   table1 "USize.ofNat" xs sh (fun n => toString (USize.ofNat n)),
   table1 "UInt8.ofBitVec" xs sh (fun n => toString (UInt8.ofBitVec (BitVec.ofNat 8 n))),
   table1 "UInt16.ofBitVec" xs sh (fun n => toString (UInt16.ofBitVec (BitVec.ofNat 16 n))),
   table1 "UInt32.ofBitVec" xs sh (fun n => toString (UInt32.ofBitVec (BitVec.ofNat 32 n))),
   table1 "UInt64.ofBitVec" xs sh (fun n => toString (UInt64.ofBitVec (BitVec.ofNat 64 n))),
   table1 "USize.ofBitVec" xs sh
     (fun n => toString (USize.ofBitVec (BitVec.ofNat System.Platform.numBits n))),
   table1 "Bool.toUIntN" [s == 0, s != 0] toString
     (fun b => s!"{b.toUInt8} {b.toUInt16} {b.toUInt32} {b.toUInt64} {b.toUSize}")]

def tables (seed : Nat) : List Table :=
  intSections seed ++ natSections seed ++ u8Sections seed ++ u16Sections seed ++
  u32Sections seed ++ u64Sections seed ++ usizeSections seed ++ conversionSections seed

def tableCount (seed : Nat) : Nat := (tables seed).length

def rowCount (i seed : Nat) : Nat := ((tables seed)[i]?.map (·.rows)).getD 0

def row (i r seed : Nat) : String := ((tables seed)[i]?.map (·.row r)).getD ""
