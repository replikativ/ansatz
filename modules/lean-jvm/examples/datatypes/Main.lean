import Eval

namespace DatatypeExample

def byteTotal (left right : ByteArray) : Nat := left.size + right.size

def ioEcho (tree : Tree) : IO Tree := do
  IO.println s!"value={eval tree}"
  pure tree

def ioCheckedEcho (tree : Tree) : IO Tree := do
  if eval tree == 0 then
    throw (IO.userError "zero-valued expression")
  pure tree

end DatatypeExample

def main : IO Unit := do
  let tree := DatatypeExample.sample 11
  let stats := DatatypeExample.summarize tree
  IO.println s!"value={stats.value}; simplified={DatatypeExample.eval (DatatypeExample.simplify tree)}; nodes={stats.nodes}; depth={stats.depth}; leaves={stats.leaves}"
