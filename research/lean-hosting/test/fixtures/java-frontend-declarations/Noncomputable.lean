prelude
axiom HostedA : Sort 1
noncomputable def hostedId (x : HostedA) : HostedA := x
noncomputable def hostedIdAgain (x : HostedA) : HostedA := hostedId x
