import Syntax

namespace DatatypeExample

def evalOp : Op → Nat → Nat → Nat
  | .add, left, right => left + right
  | .multiply, left, right => left * right

def eval : Tree → Nat
  | .literal value => value
  | .binary op left right => evalOp op (eval left) (eval right)
  | .choose condition whenTrue whenFalse =>
      if condition then eval whenTrue else eval whenFalse

def simplify : Tree → Tree
  | .literal value => .literal value
  | .choose condition whenTrue whenFalse =>
      if condition then simplify whenTrue else simplify whenFalse
  | .binary op left right =>
      let left := simplify left
      let right := simplify right
      match left, right with
      | .literal a, .literal b => .literal (evalOp op a b)
      | _, _ => .binary op left right

def nodeCount : Tree → Nat
  | .literal _ => 1
  | .binary _ left right => 1 + nodeCount left + nodeCount right
  | .choose _ whenTrue whenFalse => 1 + nodeCount whenTrue + nodeCount whenFalse

def treeDepth : Tree → Nat
  | .literal _ => 1
  | .binary _ left right => 1 + max (treeDepth left) (treeDepth right)
  | .choose _ whenTrue whenFalse => 1 + max (treeDepth whenTrue) (treeDepth whenFalse)

def containsChoice : Tree → Bool
  | .literal _ => false
  | .binary _ left right => containsChoice left || containsChoice right
  | .choose _ _ _ => true

def leafValues : Tree → List Nat
  | .literal value => [value]
  | .binary _ left right => leafValues left ++ leafValues right
  | .choose _ whenTrue whenFalse => leafValues whenTrue ++ leafValues whenFalse

def summarize (tree : Tree) : Stats :=
  ⟨"expression", eval tree, nodeCount tree, treeDepth tree, containsChoice tree, leafValues tree⟩

def readStats (stats : Stats) : List Nat :=
  [stats.value, stats.nodes, stats.depth, if stats.hasChoice then 1 else 0,
   stats.leaves.length, stats.leaves.foldl (· + ·) 0, stats.label.utf8ByteSize]

end DatatypeExample
