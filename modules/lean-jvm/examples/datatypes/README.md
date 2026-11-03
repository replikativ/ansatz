# Expression datatypes application

This Ansatz-authored integration example is independent of the datatype oracle
fixtures. It uses ordinary Lean declarations across three modules. `Syntax`
defines an operation enum, a recursive expression tree and a summary record;
`Eval` evaluates, simplifies and inspects them; `Main` supplies ordinary IO.
There are no handwritten schemas, binding adapters or custom externs.
Private source preparation and native-free public Project checks have passed.
The [application-JAR consumer](../../consumer/NominalSmoke.java) is prepared;
its isolated launch and independent native comparison remain pending.

Use `Main` as the root module. Select these entries with the native automatic
signature profile:

| Entry | Lean type | Observation |
| --- | --- | --- |
| `DatatypeExample.sample` | `Nat → Tree` | Construct an expression from a seed |
| `DatatypeExample.eval` | `Tree → Nat` | Evaluate the selected conditional branches |
| `DatatypeExample.simplify` | `Tree → Tree` | Eliminate conditionals and fold literal arithmetic |
| `DatatypeExample.summarize` | `Tree → Stats` | Inspect the entire syntax, including unselected branches |
| `DatatypeExample.readStats` | `Stats → List Nat` | Read a native or host-constructed record |
| `DatatypeExample.byteTotal` | `ByteArray → ByteArray → Nat` | Sum the two logical byte extents |
| `DatatypeExample.ioEcho` | `Tree → IO Tree` | Print its value and return the original tree |
| `DatatypeExample.ioCheckedEcho` | `Tree → IO Tree` | Reject zero-valued expressions with `IO.userError` |
| `main` | `IO Unit` | Print the fixed sample's observations |

For `sample 11`, `eval` returns `33`, `simplify` returns `Tree.literal 33`, and
`summarize` returns fields in this order:

```text
label="expression", value=33, nodes=9, depth=4,
hasChoice=true, leaves=[11, 9, 7, 0, 3]
```

`readStats` returns `[33, 9, 4, 1, 5, 30, 10]`. `ioEcho` returns the same logical
tree and prints `value=33` followed by a newline. `ioCheckedEcho` accepts that
tree; given `Tree.literal 0`, it raises the guest error `zero-valued expression`.
The sample contains every tree and operation constructor, with both true and
false conditional branches. Summary traversal includes all branches; evaluation
and simplification follow the selected branches.

The expected `main` output is:

```text
value=33; simplified=33; nodes=9; depth=4; leaves=[11, 9, 7, 0, 3]
```

Host construction should use the selected function's native-derived `LeanType`
and constructor descriptors. Useful independent checks include a host-built
`binary add (literal 4) (literal 5)` evaluating to `9`, a host-built
`choose false (literal 4) (literal 5)` evaluating to `5`, and a host-built
`Stats` with fields `("host", 17, 3, 2, false, [8, 9])` producing
`[17, 3, 2, 0, 2, 17, 4]` through `readStats`. Reuse unchanged returned values
after closing the producing Project in a fresh compatible Project, and compare
explicitly materialized values with these observations.

For aggregate input checks, two distinct `LeanBytes` values of 600,000 bytes each
exceed the combined 1 MiB payload budget. Refuse that call before execution with
`ResourceLimit`, then confirm the Project still evaluates the sample to `33`.
Passing the same immutable `LeanBytes` value twice shares its certified payload
and should return `1200000` from `byteTotal`.
