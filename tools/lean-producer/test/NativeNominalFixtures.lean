/- Closed ordinary data only; no handwritten schema or bindings. -/
namespace NativeNominalFixtures

inductive Op where
  | add
  | multiply

inductive AST where
  | literal (value : Nat)
  | binary (op : Op) (left right : AST)
  | sequence (children : List AST)
  | packed (children : Array AST)

universe u
structure Box (α : Type u) where
  value : α

structure Mixed where
  label : String
  count : UInt32
  checksum : UInt64
  index : USize
  weight : Float32
  measure : Float
  enabled : Bool
  character : Char
  trivial : Unit
  boxed : Box UInt32
  product : Prod (Box UInt32) Unit
  items : Array (Box UInt32)
  payload : ByteArray
  order : Ordering

structure Scalars where
  narrow : UInt8
  wide : UInt64
  index : USize
  weight : Float32

structure Empty where

inductive Singleton where
  | only

structure Dependent where
  size : Nat
  item : Fin size

structure ProofBearing where
  valid : True

end NativeNominalFixtures
