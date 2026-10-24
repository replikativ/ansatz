# Scoped full declaration evidence

`ansatz.export.storage/full-ci-evidence` reconstructs complete declarations for
an explicit vector of kernel `Name` values from the immutable PSS roots captured
when `load-env` created an environment. It does not admit declarations, replace
the environment, open a store, follow the branch's current head, or activate
companion metadata. The existing store lifetime must cover the call.

The normal proving view can retain its `:defs-only` body policy. Full evidence
uses an invocation-local expression cache and does not populate that view's
declaration cache with full proof bodies. Its result is
`{:constants {name ConstantInfo} :usage {...}}`; callers can release the full
proofs after their comparison. The original environment and its entries remain
unchanged.

Every call supplies all of these positive integer limits:

| Limit | Accounted scope |
| --- | --- |
| `:declarations` | Number of distinct requested declarations |
| `:shell-items` | CI shell maps, map keys, values and vector elements |
| `:expr-nodes`, `:expr-edges` | Distinct reachable expression IDs and their child references |
| `:expr-depth` | Longest expression path, including its root |
| `:raw-bytes` | Sum of reachable binary expression-record lengths |
| `:name-nodes`, `:name-chars`, `:name-depth` | Reachable Name objects, string characters and longest prefix chain |
| `:level-nodes`, `:level-depth` | Reachable Level objects and longest level path |

Name and Level sharing is counted by identity; expression sharing is counted by
stored ID. Depth limits are at most 256 because existing structural equality and
some kernel constructors recurse. There is no automatic budget increase or
unrestricted full-body fallback.

The entire requested raw expression closure is validated before constructing
its first `Expr`. Missing IDs, cycles, unknown tags, malformed record lengths,
invalid binder information and invalid UTF-8 fail the call. The actual stored
binary format is the format written by `ExprStore`, including its existing
metadata erasure. "Full" here means complete within that stored representation;
it cannot recover Lean annotations already erased by the exporter/store. Kernel
checking remains a separate operation.

PSS node IO already deserializes CI shells, Names and Levels. These limits bound
the reachable retained evidence and expression construction, **not** all
allocation performed inside the underlying PSS/CBOR decoder. This API is for
already admitted store infrastructure, not arbitrary untrusted binary files.

Evidence is tied to the actual external lookup and visibility-function
identities. Copying environment extensions onto a different external view does
not authorize the old evidence source. A requested local declaration is refused,
including a local theorem with an omitted body: the caller must compare the
actual local entry, rather than substitute an older store proof. Hidden names are
also refused. Legacy branches without a captured PSS expression DAG have no
bounded evidence source.

This is a prerequisite for exact WF supplement overlap checking. WF's existing
absent-only replay and companion activation are not changed by this API.
