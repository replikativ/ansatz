# Data/schema lifting → ansatz (the code/data/schema trichotomy)

## Why

ansatz already lifts Clojure **code** into the kernel (`ansatz.surface.*`). The Clojure **data** universe
(`Value`/EDN) and **schema** bridge (malli→type) are the same mandate — "express verified Clojure in the
kernel" — but currently live in wandler (`wandler/surface/edn.clj`, `surface/malli.clj`), tangled with the
optimizing algebra. They are NOT transducer/reducer-specific. Move them down to ansatz so:

- **ansatz = verified Clojure** — kernel + the complete Clojure↔kernel bridge across **code · data · schema**,
  spanning the full gradual spectrum (static kernel types AND dynamic `Value` + conformance). The #8 functor
  (`schema → Subtype Value γ`) is the static↔dynamic bridge = gradual-type ascription. Usable without wandler.
- **wandler = verified Clojure, optimized** — collection/relational/streaming algebra + optimizer/planner/cost,
  built on ansatz. Litmus: "transducer/reducer/query-specific?" → yes = wandler; no = ansatz.

Decision (Option 2 + 3, no backwards compat): unify the schema bridge AND structure as the trichotomy.

## Target layout (ansatz)

- `ansatz.surface.{ingest,elaborate,term,api,match,lean,pp}` — the **code** leg (unchanged).
- `ansatz.surface.data` — the **data** leg: the `Value` inductive + ops + native-Clojure-over-Value surface
  + the `edn->value`/`value->edn` boundary. (Moved from `wandler/surface/edn.clj`.) Opt-in installer.
- `ansatz.surface.schema` — the **schema** leg: the UNIFIED malli bridge. For a schema, three outputs:
  `schema->type-expr` (precise type), `schema->conforms` (Value→Bool predicate), `schema->value-type`
  (#8, `Subtype Value γ`) + reverse `type->malli`. (Absorbs today's `ansatz.malli` + the conformance
  compiler from wandler.) Planner-specific `malli-record` STAYS in wandler.

## Cross-cutting decisions

- **Install model**: `Value` is env-state → opt-in `ansatz.surface.data/install!` (today's `install-core!`),
  NOT forced into base `init!`. wandler's `install!` calls it.
- **Regex `:re`**: a SEAM — `ansatz.surface.data`/schema exposes a hook (`*re-conforms-leaf*`); `wandler.regex`
  fills it on install (Brzozowski matcher = verified library → stays wandler). Layering stays clean (ansatz
  never depends on wandler).
- **`Bool.*` codegen** the conforms fns need (`Bool.not`→`not`) become ansatz builtins (Init kernel ops anyway).

## Stages (each gates ansatz + wandler independently)

0. [this doc] design + gaps tracker (`docs/PROGRAMMING_MODEL_GAPS.md`). DONE.
1. **Value universe** → `ansatz.surface.data`; resolve `head-name` + `Bool` codegen; add regex seam. Gate.
2. **Conformance compiler** → `ansatz.surface.schema`. Gate.
3. **#8 `schema->value-type`** + unify precise/conforms/value-subtype + reverse export into
   `ansatz.surface.schema`; relocate the #8 test into ansatz. Gate.
4. **Fix recursive-conforms WF** in ansatz, WITH a real test (revives the untested path). Gate.
5. wandler re-points to `ansatz.surface.{data,schema}`, drops moved code, `install!` delegates,
   keeps `malli-record` + regex seam fill. Gate both repos.
