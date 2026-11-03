namespace DatatypeExample

inductive Op where
  | add
  | multiply

inductive Tree where
  | literal (value : Nat)
  | binary (op : Op) (left right : Tree)
  | choose (condition : Bool) (whenTrue whenFalse : Tree)

structure Stats where
  label : String
  value : Nat
  nodes : Nat
  depth : Nat
  hasChoice : Bool
  leaves : List Nat

def sample (seed : Nat) : Tree :=
  .binary .multiply
    (.binary .add
      (.choose true (.literal seed) (.literal 9))
      (.choose false (.literal 7) (.literal 0)))
    (.literal 3)

end DatatypeExample
