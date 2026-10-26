# Preserving callers around a compiled tail region

Status: implementation proposal following the frame-free M3c baseline. This
document grants no new source, kernel, native ABI or hosted acceptance authority.

Lean's boxed entrypoints normally unbox arguments, call the unboxed function,
box its result, and return. The call retains a real caller frame. Rejecting that
frame keeps the M3c baseline correct but prevents its scalar optimization from
helping ordinary boxed public calls.

The extension retains the existing mutable frame deque throughout the region.
It does not compile the caller, flatten continuations, capture a World in code,
or invent a second stack. The existing `call-values!` tail-entry operation keeps
the deque; ordinary `deliver!` pops one real caller and restores its locals,
joins and continuation. Stop the compiled region immediately after that return,
even if the restored caller is still running. Existing drivers consume the
remaining fuel.

Read the caller depth from the current Machine once per invocation. The emitted
function must never retain a depth or frame from a previous invocation. Keep
exact parameter-local, unsigned-carrier, code identity, register width, empty
current-entry joins, layout, ownership and helper-generation guards. Decline
malformed states whose historical maximum frame depth is below the actual
depth. A represented local peak becomes `caller-depth + local-peak`; inline
non-tail scalar ABI calls add one, while tail transfers add none. Preserve any
larger historical peak.

Quantum yields, short budgets, missing cases and checked counter overflow retain
the exact real caller deque. Uncommitted pure chunks may be abandoned only at
their canonical entry; remaining fuel runs through the existing interpreter.
There is no permission to replay caller effects or a host callback.

Acceptance requires full World and numeric-carrier parity against reference and
mutable execution at every small fuel prefix, including saved siblings. Cover
one and two callers with saved dead locals and lexical joins, asymmetric mutual
tail calls, terminal intrinsic tails, a historical peak larger than the actual
depth, 4096-chunk yields, short budgets and missing cases after a committed
chunk. Assert that the typed artifact itself returned `:specialized`; compilation
counts alone are insufficient. Reused code across different caller stacks must
not capture either stack. Include a genuine exported boxed wrapper before
claiming actual Lean boxed-path coverage; hand-built canonical callers are only
hosted control-flow tests. Recheck helper redefinitions and compile refusal.

The M3c warming benchmark remains its original immutable measurement. This
increment needs its own source pins and test receipt, and makes no new frontend
performance or current-cohort integration claim.
