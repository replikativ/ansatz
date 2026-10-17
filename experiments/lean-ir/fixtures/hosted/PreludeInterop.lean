prelude

@[extern "ansatz_host_identity"]
opaque hostIdentity.{u} (α : Sort u) (x : α) : α := x

def interopAnswer.{u} (α : Sort u) (x : α) : α := hostIdentity α x
