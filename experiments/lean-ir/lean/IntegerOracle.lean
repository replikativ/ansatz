import Lean

/- Native oracle for the explicit 64-bit guest profile.
   Regenerate: lean +leanprover/lean4:v4.33.1 --run lean/IntegerOracle.lean
   Decimal strings preserve integers beyond JavaScript's exact Number range.
   Signed machine integers are reported in their unsigned IR carrier encoding.
   jsExact also checks intermediate arithmetic, not just the wrapped result. -/

open Lean

private def safe (n : Int) : Bool := n.natAbs ≤ 9007199254740991

private def emit (symbol : String) (args : Array Int) (expected : Int)
    (intermediateSafe := true) (proof := false) : IO Unit := do
  let jsExact := intermediateSafe && args.all safe && safe expected
  let args := args.map fun n => toJson (toString n)
  let args := if proof then args.push Json.null else args
  IO.println <| (Json.mkObj [("symbol", toJson symbol), ("args", Json.arr args),
    ("expected", toJson (toString expected)), ("jsExact", toJson jsExact)]).compress

private def naturals (width : Nat) : Array Nat :=
  #[0, 1, 2^(width-1)-1, 2^(width-1), 2^width-1, 2^width, 2^width+1, 2^100+257]

private def unsigned (stem : String) (width : Nat) (convert : Nat → Nat) : IO Unit := do
  for n in naturals width do
    emit s!"lean_{stem}_of_nat" #[n] (convert n)
    -- Same conversion value; raw _mk consumes the Nat in lean.h.
    emit s!"lean_{stem}_of_nat_mk" #[n] (convert n)

private def casts (source : String) (width : Nat)
    (targets : Array (String × (Nat → Nat))) : IO Unit := do
  let inputs := naturals width ++ #[255, 256, 65535, 65536, 4294967295,
    4294967296, 9007199254740991, 9007199254740992, 9007199254740993]
  for (target, convert) in targets do
    for n in inputs do
      if n < 2^width then emit s!"lean_{source}_to_{target}" #[Int.ofNat n] (convert n)

private def signed {α : Type} (stem : String) (width : Nat)
    (ofNat : Nat → α) (ofInt : Int → α) (toBits : α → Nat) (toInt : α → Int)
    (neg : α → α) (add sub mul : α → α → α) : IO Unit := do
  let modulus : Nat := 2^width
  let half : Nat := 2^(width-1)
  for n in naturals width do
    emit s!"lean_{stem}_of_nat" #[n] (toBits (ofNat n))
  for n in #[-(2^100 : Int)-257, -(modulus : Int)-1, -(half : Int)-1,
               -1, 0, half, (modulus : Int)+1] do
    emit s!"lean_{stem}_of_int" #[n] (toBits (ofInt n))
  for n in (#[0, 1, half-1, half, modulus-1] : Array Nat) do
    emit s!"lean_{stem}_to_int" #[n] (toInt (ofNat n))
    emit s!"lean_{stem}_neg" #[n] (toBits (neg (ofNat n)))
  for (a, b) in (#[(0, 1), (modulus-1, 1), (half-1, 1),
                   (half, modulus-1), (modulus-1, modulus-1), (3, 5)] : Array (Nat × Nat)) do
    emit s!"lean_{stem}_add" #[a, b] (toBits (add (ofNat a) (ofNat b))) (safe ((a : Int)+b))
    emit s!"lean_{stem}_sub" #[a, b] (toBits (sub (ofNat a) (ofNat b))) (safe ((a : Int)-b))
    emit s!"lean_{stem}_mul" #[a, b] (toBits (mul (ofNat a) (ofNat b))) (safe ((a : Int)*b))

def main : IO Unit := do
  unless System.Platform.numBits == 64 do throw <| IO.userError "Integer oracle requires 64-bit Lean"
  unsigned "uint8" 8 (fun n => (UInt8.ofNat n).toNat)
  unsigned "uint16" 16 (fun n => (UInt16.ofNat n).toNat)
  unsigned "uint32" 32 (fun n => (UInt32.ofNat n).toNat)
  unsigned "uint64" 64 (fun n => (UInt64.ofNat n).toNat)
  unsigned "usize" 64 (fun n => (USize.ofNat n).toNat)
  casts "uint8" 8 #[
    ("uint16", fun n => (UInt8.ofNat n).toUInt16.toNat),
    ("uint32", fun n => (UInt8.ofNat n).toUInt32.toNat),
    ("uint64", fun n => (UInt8.ofNat n).toUInt64.toNat),
    ("usize", fun n => (UInt8.ofNat n).toUSize.toNat)]
  casts "uint16" 16 #[
    ("uint8", fun n => (UInt16.ofNat n).toUInt8.toNat),
    ("uint32", fun n => (UInt16.ofNat n).toUInt32.toNat),
    ("uint64", fun n => (UInt16.ofNat n).toUInt64.toNat),
    ("usize", fun n => (UInt16.ofNat n).toUSize.toNat)]
  casts "uint32" 32 #[
    ("uint8", fun n => (UInt32.ofNat n).toUInt8.toNat),
    ("uint16", fun n => (UInt32.ofNat n).toUInt16.toNat),
    ("uint64", fun n => (UInt32.ofNat n).toUInt64.toNat),
    ("usize", fun n => (UInt32.ofNat n).toUSize.toNat)]
  casts "uint64" 64 #[
    ("uint8", fun n => (UInt64.ofNat n).toUInt8.toNat),
    ("uint16", fun n => (UInt64.ofNat n).toUInt16.toNat),
    ("uint32", fun n => (UInt64.ofNat n).toUInt32.toNat),
    ("usize", fun n => (UInt64.ofNat n).toUSize.toNat)]
  casts "usize" 64 #[
    ("uint8", fun n => (USize.ofNat n).toUInt8.toNat),
    ("uint16", fun n => (USize.ofNat n).toUInt16.toNat),
    ("uint32", fun n => (USize.ofNat n).toUInt32.toNat),
    ("uint64", fun n => (USize.ofNat n).toUInt64.toNat)]
  for (a, b) in (#[(0, 0), (1, 2), (255, 256), (2^32-1, 2^32+1),
      (2^52, 2^52-1), (2^53-1, 1), (2^63, 2^63), (2^64-1, 1),
      (2^64-1, 2^64-1)] : Array (Nat × Nat)) do
    let x := UInt64.ofNat a
    let y := UInt64.ofNat b
    emit "lean_uint64_add" #[a, b] (x+y).toNat (safe ((a : Int)+b))
    emit "lean_uint64_sub" #[a, b] (x-y).toNat (safe ((a : Int)-b))
    emit "lean_uint64_mul" #[a, b] (x*y).toNat (safe ((a : Int)*b))
    emit "lean_uint64_land" #[a, b] (x &&& y).toNat
    emit "lean_uint64_lor" #[a, b] (x ||| y).toNat
  for (a, b) in (#[(0, 0), (0, 63), (255, 8), (255, 48), (255, 56),
      (1, 52), (1, 53), (1, 63), (1, 64), (3, 65), (255, 128),
      (2^63, 1), (2^64-1, 63), (1, 2^64-1)] : Array (Nat × Nat)) do
    emit "lean_uint64_shift_left" #[a, b]
      ((UInt64.ofNat a) <<< (UInt64.ofNat b)).toNat
      (safe ((a : Int) * (2 : Int)^(b % 64)))
  emit "lean_uint8_of_nat" #[42] (UInt8.ofNatLT 42 (by decide)).toNat true true
  emit "lean_uint16_of_nat" #[42] (UInt16.ofNatLT 42 (by decide)).toNat true true
  emit "lean_uint32_of_nat" #[42] (UInt32.ofNatLT 42 (by decide)).toNat true true
  emit "lean_uint64_of_nat" #[42] (UInt64.ofNatLT 42 (by decide)).toNat true true
  emit "lean_usize_of_nat" #[42]
    (USize.ofNatLT 42 (Nat.lt_of_lt_of_le (show 42 < 4294967296 by decide) USize.le_size)).toNat true true
  signed "int8" 8 Int8.ofNat Int8.ofInt (fun n => n.toUInt8.toNat) Int8.toInt
    (fun a => -a) (fun a b => a+b) (fun a b => a-b) (fun a b => a*b)
  signed "int16" 16 Int16.ofNat Int16.ofInt (fun n => n.toUInt16.toNat) Int16.toInt
    (fun a => -a) (fun a b => a+b) (fun a b => a-b) (fun a b => a*b)
  signed "int32" 32 Int32.ofNat Int32.ofInt (fun n => n.toUInt32.toNat) Int32.toInt
    (fun a => -a) (fun a b => a+b) (fun a b => a-b) (fun a b => a*b)
  signed "int64" 64 Int64.ofNat Int64.ofInt (fun n => n.toUInt64.toNat) Int64.toInt
    (fun a => -a) (fun a b => a+b) (fun a b => a-b) (fun a b => a*b)
  signed "isize" 64 ISize.ofNat ISize.ofInt (fun n => n.toUSize.toNat) ISize.toInt
    (fun a => -a) (fun a b => a+b) (fun a b => a-b) (fun a b => a*b)
  for (a, b) in #[(-7, 3), (-9223372036854775808, 9223372036854775807),
                   (-(2^100), 2^100+1), (9007199254740991, 1), (0, 0)] do
    emit "lean_int_sub" #[a, b] (a-b)
    emit "lean_int_mul" #[a, b] (a*b)
    emit "lean_int_dec_eq" #[a, b] (if a == b then 1 else 0)
    emit "lean_int_dec_le" #[a, b] (if a ≤ b then 1 else 0)
  for (a, b) in (#[(2, 9007199254740991), (9007199254740991, 2),
                   (0, 9007199254740991), (42, 0)] : Array (Nat × Nat)) do
    emit "lean_nat_mod" #[a, b] (a % b)
  for (a, b) in (#[(0, 0), (255, 15), (3735928559, 4042322160),
                   (2^52+5, 2^51+3), (2^100+15, 2^99+3)] : Array (Nat × Nat)) do
    emit "lean_nat_land" #[a, b] (Nat.land a b)
    emit "lean_nat_lor" #[a, b] (Nat.lor a b)
    emit "lean_nat_xor" #[a, b] (Nat.xor a b)
  -- Native safely short-circuits zero before examining a huge shift count.
  -- Nonzero huge-count host allocation rejection is tested without allocating.
  for (a, b) in (#[(0, 2^100), (0, 2147483648), (0, 2^52),
                   (1, 0), (3, 4), (1, 52), (1, 53), (1, 100)] : Array (Nat × Nat)) do
    emit "lean_nat_shiftl" #[a, b] (Nat.shiftLeft a b)
  for a in (#[0, 1, 2, 2147483647, 2147483648, 4294967294, 4294967295] : Array Nat) do
    for b in (#[0, 1, 2, 2147483647, 2147483648, 4294967294, 4294967295] : Array Nat) do
      emit "lean_uint32_dec_lt" #[a, b] (if UInt32.ofNat a < UInt32.ofNat b then 1 else 0)
