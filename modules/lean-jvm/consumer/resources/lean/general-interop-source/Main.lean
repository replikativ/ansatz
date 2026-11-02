import Helper
namespace Demo
def sumArgs (a b : Nat) (enabled : Bool) : Nat := if enabled then helperBump (a + b) else a
def negate (n : Int) : Int := -n
def greet (name : String) (excited : Bool) : String := name ++ (if excited then "!" else ".")
def unitIdentity (u : Unit) : Unit := u
def constantBool : Bool := true
def pairIdentity (p : Bool × Nat) : Bool × Nat := p
def pairSecond (p : Bool × Nat) : Nat := p.2
def discardList (_xs : List Nat) : Nat := 19
def reverseList (xs : List Nat) : List Nat := xs.reverse
def optionUnit (u : Option Unit) : Option Unit := u
def nestedOption (n : Option (Option Nat)) : Option (Option Nat) := n
def pairs (n : Nat) : List (Bool × Nat) := [(true, n), (false, helperBump n)]
def effect (enabled : Bool) (xs : List Nat) : IO (Option (String × Nat)) := do
  IO.println "effect"
  pure (if enabled then some ("sum", xs.foldl (· + ·) 0) else none)
def main : IO Unit := IO.println "main"
def other : IO Unit := IO.println "other"
def emptyList : List Nat := []
end Demo
