# Original Expr quickLt fixture

Two unchanged original IR rows authenticate `Lean.Expr.quickLt` and its boxed
wrapper against the pinned source index. Added fixture labels do not change raw
CAS identity. Four native hook evidence rows document existing typed decoder
semantics; they are not guest helper calls or an activation policy.

`Oracle.lean` is a safe pinned-source comparison oracle. Its 25 expected lines
cover genuine constructors, Eqv binder behavior, metadata ordering and real
metadata-derived hash collisions. Projection index0 versus2^64 intentionally
collides under the source constructor's UInt64 hash narrowing; the oracle only
compares constructed Expr data and does not evaluate an ill-typed projection.
The fixture claims neither AOT execution nor native allocation/reference-count
parity. Forced-cache Java models are separate tests, not native oracle values.

See [runtime scope](../../../research/JAVA_EXPR_QUICK_ORDER_RUNTIME.md) and
`provenance.json` for pins and observed gates. No initialized global is required.
