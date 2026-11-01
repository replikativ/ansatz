import NativeStartupEvidence

open Lean NativeStartupEvidence

-- Source-selection models, not injected module metadata or execution receipts.
private def a : Name × Name := (`A, `initA)
private def b : Name × Name := (`B, `initB)
#guard regularSequence #[a, a] #[a, b, b] == #[a, a, b, b]
#guard regularSequence #[] #[b, b] == #[b, b]
#guard regularSequence #[a] #[a] == #[a]
#guard !(phaseSelected false .runtime .runtime)
#guard phaseSelected false .runtime .comptime
#guard phaseSelected false .runtime .all
#guard phaseSelected false .all .runtime
#guard phaseSelected false .comptime .runtime
#guard phaseSelected true .runtime .runtime
