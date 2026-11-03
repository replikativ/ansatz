namespace Interop

structure Message where
  count : Nat
  enabled : Bool

-- Ordinary Lean implementations are the reference on native Lean and when
-- no JVM implementation is selected. No custom axiom or foreign type is used.
@[noinline] def normalize (n : Nat) : Nat := n + 1

@[noinline] def normalizeMessage (message : Message) : Message :=
  { message with count := message.count + 1 }

@[noinline] def combine (n : Nat) (enabled : Bool) (label : String) : Message :=
  { count := n + label.length, enabled }

@[noinline] def constant : Nat := 7

@[noinline] def twice (n : Nat) : Nat := n * 2

@[noinline] def echo (xs : Array Nat) : Array Nat := xs

@[noinline] def isA (c : Char) : Bool := c == 'a'

end Interop
