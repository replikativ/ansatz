def extByte (x : UInt8) : UInt8 := x + 1
def extSigned (x : Int64) : Int64 := -x
def extDouble (x : Float) : Float := x + 0.5
def extSingle (x : Float32) : Float32 := x + 0.5
def extChar (x : Char) : Char := x
def extWord (x : USize) : USize := x + 1
def extBytes (x : ByteArray) : ByteArray := x
def extArray (x : Array Nat) : Array Nat := x
def extSum (x : Sum Bool Nat) : Sum Nat Bool := match x with
  | .inl b => .inr b
  | .inr n => .inl n
def extExcept (x : Except String Nat) : Except String Nat := x
def extConstantByte : UInt8 := 255
def extConstantFloat : Float := 1.5
def extArrayPush (xs : Array Nat) (n : Nat) : Array Nat := xs.push n
def extBytesPush (xs : ByteArray) (n : UInt8) : ByteArray := xs.push n
def extOtherMachines (x : UInt16 × (UInt32 × (Int8 × (Int16 × (Int32 × (UInt64 × ISize)))))) : UInt16 × (UInt32 × (Int8 × (Int16 × (Int32 × (UInt64 × ISize))))) := x
def extIO (xs : Array Float) : IO (Except String (Array Float)) := do
  IO.println "floats"
  pure (.ok xs)
