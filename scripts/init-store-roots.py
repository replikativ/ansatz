#!/usr/bin/env python3
"""Regenerate scripts/init-store-roots.txt -- the root manifest for the bundled Init store.

The bundled store is the transitive dependency closure of that manifest (see
scripts/regen-bundled-store.sh). This script is how the manifest itself is derived, so that
widening the tier is a reproducible operation rather than a hand edit nobody can reconstruct
-- which is exactly how the store drifted before (it was a raw `head -n 200000` of a full
`lean4export Init` dump, with no script and no record of the cut).

Roots are the union of:
  1. every declaration already in the current bundled store, so the tier only ever grows
  2. Lean's Boolean simp set -- every @[simp] lemma in Init about Bool / decide / Nat's
     Boolean relations, read off the bundled attribute corpus (see BOOL_SIMP_KEEP)
  2b. every constant simp's own `default-simp-lemmas` / `simp-only-builtins` spells
  3. the whole `Lean.Omega.*` namespace -- omega's certificate lemmas
  4. every constant named in the `omega-names` table in src/ansatz/tactic/omega_proof.clj
  5. every constant that file names inline via `(name/from-string "...")`
  6. a hand-maintained EXTRAS list (below): correct core spellings for names omega_proof.clj
     gets wrong, plus the bmod/div-bound machinery its proof builder needs

minus the EXCLUDE set, which must stay out or well-founded recursion breaks (see below).

Usage:
    python3 scripts/init-store-roots.py [FULL_INIT_NDJSON]

FULL_INIT_NDJSON is a complete `lean4export Init` dump used as the existence oracle: a root
that does not name a real constant makes lean4export abort, so unknown names are dropped
with a report. It defaults to test-data/init.ndjson; produce one with

    cd ../lean4export && lake env ./.lake/build/bin/lean4export Init > /some/scratch/init.ndjson
    python3 scripts/init-store-roots.py /some/scratch/init.ndjson

MOVE IT OUT OF test-data/ WHEN YOU ARE DONE, or pass it from a scratch path as above:
`test-data/init.ndjson` is also a TEST FIXTURE (ansatz.test-env/init-full-env and half a
dozen suites fall back to it), and its mere presence switches those tests from the 3.7k
bundled tier to the full 54k-declaration Init. That is a several-hundred-megabyte swing in
retained heap and will OOM `clj -J-Xmx3g -M:test`.

If the oracle is absent this script falls back to the bundled store plus the attribute
corpus (both of which name only real Init constants) and says so; that is enough to widen
the tier with attrs-sourced roots, and lean4export still aborts on any invented name.

Then re-run scripts/regen-bundled-store.sh to rebuild the store from the new manifest.
"""
import gzip
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.dirname(HERE)
MANIFEST = os.path.join(HERE, "init-store-roots.txt")
STORE = os.path.join(PROJECT, "resources", "ansatz", "init-medium.ndjson.gz")
OMEGA_SRC = [
    os.path.join(PROJECT, "src", "ansatz", "tactic", "omega_proof.clj"),
    os.path.join(PROJECT, "src", "ansatz", "tactic", "omega.clj"),
] + [
    os.path.join(PROJECT, "src", "ansatz", "tactic", "omega", f)
    for f in sorted(os.listdir(os.path.join(PROJECT, "src", "ansatz", "tactic", "omega")))
    if f.endswith(".clj")
]
ATTRS = os.path.join(PROJECT, "resources", "ansatz", "init-attrs.ndjson.gz")
SIMP_SRC = os.path.join(PROJECT, "src", "ansatz", "tactic", "simp.clj")
DEFAULT_ORACLE = os.path.join(PROJECT, "test-data", "init.ndjson")

# ---------------------------------------------------------------------------
# BOOLEAN SIMP SET
# ---------------------------------------------------------------------------
# ansatz inherits Lean's @[simp] corpus wholesale: scripts/dump_attrs.lean dumps every
# @[simp] name in `Init` into resources/ansatz/init-attrs.ndjson.gz, and
# ansatz.attrs/import-attrs then INTERSECTS that list with the loaded store, silently
# dropping the names the store does not carry. So a lemma missing from the store is not a
# loud error -- it is a simp set that quietly does less. Simp and grind are the only things
# that notice, and only by failing to prove goals nobody has a test for.
#
# That is precisely what happened to `Bool`: the store carried `Bool.and_eq_true`,
# `Bool.and_self`, `Bool.and_true`, `Bool.and_false` and nothing at all from the `or` half
# -- no `Bool.or_eq_true`, no `Bool.or_self`, no `Bool.true_or`/`false_or`. Since Clojure's
# `or` is the primitive every Boolean-returning predicate is built from, EVERY such function
# was unprovable: `(a && b) = true` split into a conjunction and `(a || b) = true` did not
# split at all.
#
# The rule below closes the whole family rather than the names someone happened to hit:
# take Lean's own @[simp] set (the attrs corpus is the authority -- if a name is in it, it
# exists in Init) and keep everything in the Bool / decide / Nat-Boolean-relation family.
# BOOL_SIMP_DROP removes the entries that reach outside this tier: the fixed-width integer
# and container bridges (`Bool.toBitVec_toUInt8`, `List.decide_mem_cons`, ...) and
# `Bool.sizeOf_eq_one`, which would drag in the `SizeOf` development ansatz deliberately
# ships its own copy of (see EXCLUDE).
BOOL_SIMP_KEEP = re.compile(
    r"^Bool\."                                     # the whole Bool namespace
    r"|decide"                                     # decide_*, *_decide_*, Bool.decide_*
    r"|^Nat\.(ble_eq|blt_eq|beq_eq|beq_refl)$"     # Nat's Bool relations <-> Prop
    r"|^(beq_true|beq_false|heq_eq_eq)$"
    # the decidable-branching family: `ite`/`dite`/`cond` are where a Boolean condition
    # meets a value, and ansatz's surface `if` over a comparison elaborates straight to
    # `dite`. simp.clj's own default set already NAMES `ite_true`/`ite_false`/`dite_true`/
    # `dite_false` -- and every one of them was absent from the store, i.e. the curated
    # default list was itself half dead.
    r"|^(ite|dite|cond|if|dif)_"
    r"|_(ite|dite|cond)_"
    r"|^(left|right)_(eq|iff)_(ite|dite)_iff$"
    r"|^apply_(ite|dite)$"
)
BOOL_SIMP_DROP = re.compile(
    r"toBitVec|toNat|toInt|toUInt|toISize"         # fixed-width integer bridges
    r"|BitVec|UInt|ISize|Int8|Int16|Int32|Int64|USize|Float"
    r"|^List\.|^Array\.|^Vector\.|^Option\.|^Std\."  # container bridges
    r"|^Nat\.decide_"                              # Nat bit-twiddling decision lemmas
    r"|sizeOf"                                     # would pull in SizeOf (see EXCLUDE)
)

# ---------------------------------------------------------------------------
# ansatz ships its OWN minimal `SizeOf` and `Prod.Lex` developments in
# resources/ansatz/{sizeof,lex}-prelude.ndjson.gz, and src/ansatz/wf.clj's well-founded
# recursion encoder is built against those. If the Init store also defines them the two
# collide and `:termination-by` proofs stop discharging with `:termination-wf-encode-failed`.
# The previous store excluded them only by accident of being a truncation; keep it explicit.
EXCLUDE = re.compile(
    r"(\._sizeOf_1|\._sizeOf_inst|\.sizeOf_spec)$"    # per-inductive sizeOf auxiliaries
    r"|^SizeOf(\.|$)|^instSizeOf"                      # the SizeOf class itself
    r"|^Prod\.Lex(\.|$)"                               # lexicographic order on pairs
    r"|^Lean\.Omega\.Prod\."                           # the only Lean.Omega users of Prod.Lex
)

# Correct core spellings for constants omega_proof.clj references under Mathlib names or
# typos, plus the machinery its :bmod case and add-div-bounds Int branch build terms out of.
# Shipping the correct names means fixing those references is a pure rename, no store change.
EXTRAS = [
    "Decidable.not_and_iff_not_or_not",      # for `not_and_or`
    "Classical.not_and_iff_not_or_not",
    "Classical.not_imp",                     # for `not_imp`
    "Decidable.not_imp_iff_and_not",
    "Decidable.iff_iff_and_or_not_and_not",  # for `iff_iff_and_or_not_and_not`
    "Int.ofNat_eq_natCast",                  # for `Int.ofNat.eq_def` (Int.ofNat is a ctor,
                                             # so it has no equation lemma)
    # bmod (hard-equality elimination) support -- Lean.Omega.bmod_sat's statement and the
    # terms extract-proof's :bmod case assembles around it
    "Lean.Omega.Coeffs.bmod",
    "Lean.Omega.Coeffs.bmod_length",
    "Lean.Omega.Coeffs.bmod_dot_sub_dot_bmod",
    "Lean.Omega.Coeffs.dvd_bmod_dot_sub_dot_bmod",
    "Lean.Omega.Coeffs.get",
    "Lean.Omega.Coeffs.set",
    "of_decide_eq_true",
    "Decidable.decide",
    "Nat.decLe",
    "List.length",
    "instHMul", "instHAdd", "Int.instMul", "Int.instAdd",
    # Int division/modulo bounds (omega_proof.clj's add-div-bounds Int branch)
    "Int.mul_ediv_self_le", "Int.lt_mul_ediv_self_add",
    "Int.emod_emod_of_dvd", "Int.ediv_add_emod",
]

HEADER = """\
# Root manifest for the bundled "medium" Init store. GENERATED by scripts/init-store-roots.py
# -- edit EXTRAS/EXCLUDE there rather than hand-editing this file.
#
# The bundled store (resources/ansatz/init-medium.ndjson.gz) is the transitive dependency
# closure of these roots, produced by scripts/regen-bundled-store.sh. Closure under
# dependencies is guaranteed by lean4export, so the export always replays cleanly through
# the ansatz kernel. Blank lines and `#` comments are ignored; everything else is passed to
# lean4export after a `--` separator and must name a constant that exists in `Init` at the
# toolchain pinned in ../lean4export/lean-toolchain (currently leanprover/lean4:v4.29.0-rc2).
#
# Five names referenced by omega_proof.clj do NOT exist in Lean core's `Init` under those
# spellings -- they are Mathlib spellings or typos -- and so cannot be roots. The correct
# core constants ARE in this manifest, so fixing each reference is a rename with no store
# change needed:
#
#   omega_proof.clj spelling            core constant shipped here
#   ----------------------------------  ------------------------------------------
#   not_and_or                          Decidable.not_and_iff_not_or_not
#                                       Classical.not_and_iff_not_or_not
#   not_imp                             Classical.not_imp
#                                       Decidable.not_imp_iff_and_not
#   iff_iff_and_or_not_and_not          Decidable.iff_iff_and_or_not_and_not
#   Int.ofNat.eq_def                    Int.ofNat_eq_natCast
#   Lean.Omega.Coeffs.bmod_coeffs       Lean.Omega.bmod_coeffs  (already a root; this is
#                                       the name `Lean.Omega.bmod_sat`'s own statement uses)
#
# DELIBERATE OMISSIONS -- do not "helpfully" add these. ansatz ships its own minimal
# `SizeOf` and `Prod.Lex` developments in resources/ansatz/{sizeof,lex}-prelude.ndjson.gz,
# and src/ansatz/wf.clj's well-founded recursion encoder is built against those. If the Init
# store also defines them the two collide and `:termination-by` proofs stop discharging with
# `:termination-wf-encode-failed`. The closure therefore excludes SizeOf and its instances,
# every `*._sizeOf_1` / `*._sizeOf_inst` / `*.sizeOf_spec` auxiliary, `Prod.Lex` and its
# eliminators, and `Lean.Omega.Prod.of_lex` / `of_not_lex`. The previous store excluded
# these too -- by accident, being a truncation -- which is why the dependency went unnoticed.
#
# BOOLEAN SIMP SET -- ansatz inherits Lean's @[simp] corpus, intersected with this store, so
# a Bool lemma missing here is a simp set that silently does less. The store used to carry
# `Bool.and_eq_true` and nothing from the `or` half, which made every Boolean-returning
# Clojure function (Clojure's `or` is the primitive they are all built from) unprovable. The
# whole Bool/decide family is now a generated rule in scripts/init-store-roots.py, and
# test/ansatz/tactic/tactic_constants_test.clj asserts it stays resolvable.
"""

DECL_KEYS = ("def", "thm", "axiom", "opaque", "quot")


def _open(path):
    if path.endswith(".gz"):
        return io.TextIOWrapper(gzip.open(path, "rb"), encoding="utf-8")
    return open(path, encoding="utf-8")


def declarations(path, roots_only=False):
    """Yield the constant names declared by a lean4export NDJSON dump. With roots_only,
    yield inductive type names but not their constructors/recursors (lean4export re-derives
    those from the type, and they are not valid standalone roots)."""
    names = {0: ""}
    with _open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            if "in" in obj:
                idx = obj["in"]
                if "str" in obj:
                    pre = names.get(obj["str"]["pre"], "")
                    part = obj["str"]["str"]
                elif "num" in obj:
                    pre = names.get(obj["num"]["pre"], "")
                    part = str(obj["num"].get("i"))
                else:
                    continue
                names[idx] = (pre + "." + part) if pre else part
                continue
            for key in DECL_KEYS:
                if key in obj:
                    yield names.get(obj[key]["name"], "?")
                    break
            else:
                if "inductive" in obj:
                    blk = obj["inductive"]
                    groups = ["types"] if roots_only else ["types", "ctors", "recs"]
                    for group in groups:
                        for item in blk.get(group, []):
                            yield names.get(item["name"], "?")


def omega_names():
    """Every constant omega's proof builder names -- via omega_proof.clj's `omega-names`
    table, or inline as `(name/from-string "...")` anywhere under src/ansatz/tactic/omega*."""
    table, inline = set(), set()
    for path in OMEGA_SRC:
        src = open(path, encoding="utf-8").read()
        table |= set(re.findall(r'\(n\s+"([^"]+)"\)', src))
        inline |= set(re.findall(r'name/from-string\s+"([^"]+)"', src))
    return table, inline


def attr_names(kinds=("simp",)):
    """Every constant named by the bundled Init attribute corpus (resources/ansatz/
    init-attrs.ndjson.gz), restricted to the given attribute kinds. The corpus is dumped
    from the FULL `Init` by scripts/dump_attrs.lean, so a name appearing in it necessarily
    exists in Init -- which makes it a usable existence oracle for the simp set without the
    285 MB full dump."""
    out = set()
    if not os.path.exists(ATTRS):
        return out
    with _open(ATTRS) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            if obj.get("kind") in kinds:
                out.add(obj["name"])
    return out


def simp_default_set_names():
    """Every constant simp's own hand-curated default set spells -- `default-simp-lemmas` and
    `simp-only-builtins` in src/ansatz/tactic/simp.clj. `make-simp-lemmas` skips names that do
    not resolve, so a spelling that is not in the store is a rewrite simp silently cannot do.
    Seven of them were in exactly that state (`Nat.ble_eq`, `ite_true`, `ite_false`,
    `dite_true`, `dite_false`, `List.length_nil`, `Function.comp_id`, ...) --
    test/ansatz/tactic/tactic_constants_test.clj is the guard that keeps them resolving."""
    src = open(SIMP_SRC, encoding="utf-8").read()
    out = set()
    for var in ("default-simp-lemmas", "simp-only-builtins"):
        m = re.search(r"\(def [^\n]*" + re.escape(var) + r"\b(.*?)\n\n", src, re.S)
        if m:
            out |= set(re.findall(r'"([A-Za-z_][A-Za-z0-9_.\'₀-₉]*)"', m.group(1)))
    return out


def bool_simp_names():
    """Lean's Boolean simp set: every @[simp] lemma in Init about Bool / decide / Nat's
    Boolean relations, minus the entries that reach outside the medium tier. See the
    BOOL_SIMP_KEEP comment above for why this is a RULE and not a hand-picked list."""
    return {n for n in attr_names()
            if BOOL_SIMP_KEEP.search(n) and not BOOL_SIMP_DROP.search(n)}


def main():
    oracle = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_ORACLE
    bool_simp = bool_simp_names()
    if os.path.exists(oracle):
        exists = set(declarations(oracle))
    else:
        # Fall back to the two name sets we already ship that are known to name real Init
        # constants: the current store (it was exported from Init) and the attribute corpus
        # (dumped from Init). Enough to widen the tier with attrs-sourced roots; a root from
        # EXTRAS that does not exist would still be caught by lean4export aborting.
        exists = set(declarations(STORE)) | attr_names(("simp", "unfold", "csimp", "extern", "impl"))
        print(f"  NOTE: {oracle} not found -- using the bundled store + attrs corpus as the\n"
              f"        existence oracle. Roots outside those two sets are kept unchecked and\n"
              f"        lean4export will abort on any that do not exist.", file=sys.stderr)

    report = {}

    roots = set(declarations(STORE, roots_only=True))
    report["current store"] = len(roots)

    roots |= bool_simp
    report["Bool/decide @[simp] set"] = len(bool_simp)

    simp_defaults = simp_default_set_names()
    roots |= simp_defaults
    report["simp's default set"] = len(simp_defaults)

    omega_ns = {n for n in exists if n.startswith("Lean.Omega.")}
    roots |= omega_ns
    report["Lean.Omega.*"] = len(omega_ns)

    table, inline = omega_names()
    roots |= table | inline
    report["omega-names table"] = len(table)
    report["omega inline refs"] = len(inline)

    roots |= set(EXTRAS)
    report["extras"] = len(EXTRAS)

    excluded = sorted(n for n in roots if EXCLUDE.search(n))
    roots -= set(excluded)
    report["excluded (prelude clash)"] = len(excluded)

    present = sorted(n for n in roots if n in exists)
    absent = sorted(n for n in roots if n not in exists)

    for key, val in report.items():
        print(f"  {key:<26} {val}", file=sys.stderr)
    print(f"  {'roots written':<26} {len(present)}", file=sys.stderr)
    print(f"  {'dropped (not in Init)':<26} {len(absent)}", file=sys.stderr)
    for name in absent:
        print(f"    ABSENT {name}", file=sys.stderr)

    with open(MANIFEST, "w", encoding="utf-8") as fh:
        fh.write(HEADER)
        for name in present:
            fh.write(name + "\n")
    print(f"wrote {len(present)} roots to {MANIFEST}", file=sys.stderr)


if __name__ == "__main__":
    main()
