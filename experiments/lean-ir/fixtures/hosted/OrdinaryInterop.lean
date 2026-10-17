@[extern "ansatz_host_identity"]
opaque ordinaryHostIdentity.{u} (α : Sort u) (x : α) : α := x

def ordinaryInteropRoundTrip.{u} (α : Sort u) (x : α) : α :=
  ordinaryHostIdentity α x
