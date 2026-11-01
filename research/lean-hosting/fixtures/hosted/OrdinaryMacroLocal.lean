import ResidentNativeA
macro "hostedIdentity" : term => `(fun x => x)

def macroAnswer.{u} (α : Sort u) (x : α) : α := hostedIdentity x

def localMacroAnswer : Nat := macroAnswer Nat 42
