-- Lean 4.33.1: @[extern] primitives run natively (src/include/lean/lean.h,
-- src/runtime/object.cpp, src/runtime/hash.cpp). test/ansatz/extern_runtime_test.clj
-- asserts the same values for the Clojure backend. Check with
--   lean +leanprover/lean4:v4.33.1 test/lean/extern_runtime.lean

-- String: a sequence of code points, UTF-8 underneath.
example : "a😀" ++ "b" = "a😀b" := by native_decide
example : "h😀é".toList.map Char.toNat = [104, 128512, 233] := by native_decide
example : String.ofList ['h', '😀', 'é'] = "h😀é" := by native_decide
example : "h😀é".length = 3 := by native_decide
example : "h😀é".utf8ByteSize = 7 := by native_decide
example : "h😀é".toByteArray.data.toList.map UInt8.toNat = [104, 240, 159, 152, 128, 195, 169] := by native_decide
example : "".toList = [] := by native_decide
-- lean_string_lt is memcmp on UTF-8, i.e. code-point order (U+FFFF < U+1F600),
-- unlike UTF-16 comparison (0xFFFF > 0xD83D).
example : decide ("￿" < "😀") = true := by native_decide
example : decide ("abc" < "abd") = true := by native_decide
example : decide ("ab" < "abc") = true := by native_decide
example : decide ("abc" < "ab") = false := by native_decide
example : decide ("abc" < "abc") = false := by native_decide
example : "hello".hash = 9821865621596011261 := by native_decide
example : "".hash = 9877294847684254529 := by native_decide
example : "h😀é longer than eight bytes".hash = 9139638103461449745 := by native_decide
example : mixHash 12345 67890 = 6417489475506850606 := by native_decide
example : mixHash 18446744073709551615 3 = 5887013808463828774 := by native_decide

-- Char: a valid scalar value, else Char.ofNat gives '\0'.
example : (Char.ofNat 128512).toNat = 128512 := by native_decide
example : (Char.ofNat 55296).toNat = 0 := by native_decide
example : (Char.ofNat 1114112).toNat = 0 := by native_decide
example : (Char.ofNat 57344).toNat = 57344 := by native_decide

-- Fixed-width unsigned integers wrap modulo 2^w.
example : (UInt8.ofNat 300).toNat = 44 := by native_decide
example : ((200 : UInt8) + 100).toNat = 44 := by native_decide
example : (-(1 : UInt8)).toNat = 255 := by native_decide
example : ((0xF0 : UInt8) &&& 0x3C).toNat = 0x30 := by native_decide
example : ((0xF0 : UInt8) ||| 0x0F).toNat = 255 := by native_decide
example : ((1 : UInt32) <<< 33).toNat = 2 := by native_decide
example : ((8 : UInt32) >>> 35).toNat = 1 := by native_decide
example : ((7 : UInt32) % 0).toNat = 7 := by native_decide
example : (UInt32.toUInt8 300).toNat = 44 := by native_decide
example : (USize.ofNat (2^64 + 5)).toNat = 5 := by native_decide
example : ((0 : USize) - 1).toNat = 2^64 - 1 := by native_decide
example : ((2^64 - 1 : USize) + 2).toNat = 1 := by native_decide
example : (USize.ofNat 42).repr = "42" := by native_decide
example : (UInt64.ofNat (2^63 + 1)).toNat = 2^63 + 1 := by native_decide

-- Nat bit operations on values beyond 64 bits.
example : (2^70 + 5) &&& (2^70 + 3) = 2^70 + 1 := by native_decide
example : (2^70) ||| 6 = 2^70 + 6 := by native_decide
example : (3 : Nat) <<< 70 = 3 * 2^70 := by native_decide
example : (2^70 + 2^3) >>> 3 = 2^67 + 1 := by native_decide
example : Nat.gcd (2^70 * 3) (2^65 * 9) = 2^65 * 3 := by native_decide
example : Nat.pred 0 = 0 := by native_decide

-- Array / ByteArray.
example : (#[1, 2, 3].push 4).size = 4 := by native_decide
example : (#[] : Array Nat).pop = #[] := by native_decide
example : #[1, 2, 3].pop = #[1, 2] := by native_decide
example : (#[1, 2, 3].set! 1 9) = #[1, 9, 3] := by native_decide
-- Out of bounds, set! panics (lean_array_set_panic prints "index out of bounds") and
-- returns the array unchanged; the Clojure test asserts that behaviour.
example : (ByteArray.mk #[1, 2, 3, 4, 5]).copySlice 1 (ByteArray.mk #[9, 9, 9]) 1 10
    = ByteArray.mk #[9, 2, 3, 4, 5] := by native_decide
example : (ByteArray.mk #[1, 2, 3, 4, 5]).copySlice 0 (ByteArray.mk #[9, 9, 9, 9]) 2 1
    = ByteArray.mk #[9, 9, 1, 9] := by native_decide
