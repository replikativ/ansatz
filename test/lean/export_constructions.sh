#!/usr/bin/env bash
# Rebuild the Lean v4.33.1 oracle consumed by ansatz.constructions-test.
set -euo pipefail
cd "$(dirname "$0")/../.."
constructions_bin=${LEAN_TOOLCHAIN_BIN:-"$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin"}
constructions_exporter=${LEAN4EXPORT:-"$HOME/Development/lean4export/.lake/build/bin/lean4export"}
constructions_tmp=$(mktemp -d /tmp/ansatz-constructions.XXXXXX)
trap 'rm -rf "$constructions_tmp"' EXIT
"$constructions_bin/lean" -R test/lean -o "$constructions_tmp/constructions.olean" test/lean/constructions.lean
names=(Nat List Option Prod Bool Fin Or Eq
       T10Reference.Empty T10Reference.Unit T10Reference.Enum T10Reference.Rec T10Reference.Vec T10Reference.Rose
       T10Reference.Assoc T10Reference.Disj T10Reference.Inf T10Reference.Tree T10Reference.Forest)
suffixes=('' recOn casesOn ctorIdx ctorElimType ctorElim noConfusionType noConfusion below brecOn.go brecOn brecOn.eq)
decls=()
for n in "${names[@]}"; do
  for s in "${suffixes[@]}"; do decls+=("$n${s:+.$s}"); done
done
for s in below_1 brecOn_1.go brecOn_1 brecOn_1.eq; do decls+=("T10Reference.Rose.$s"); done
for spec in 'T10Reference.Unit unit' 'Nat zero succ' 'List nil cons' 'Option none some' 'Prod mk' 'Bool false true' 'Fin mk' \
            'T10Reference.Enum a b c' 'T10Reference.Rec z s' 'T10Reference.Vec nil cons' \
            'T10Reference.Rose node' 'T10Reference.Assoc mk' 'T10Reference.Inf node' \
            'T10Reference.Tree node' 'T10Reference.Forest nil cons'; do
  read -r -a parts <<< "$spec"
  for c in "${parts[@]:1}"; do
    for s in noConfusion elim; do decls+=("${parts[0]}.$c.$s"); done
  done
done
LEAN_PATH="$constructions_tmp" PATH="$constructions_bin:$PATH" \
  "$constructions_exporter" --ignore-missing constructions -- "${decls[@]}" \
  | gzip -n > "$constructions_tmp/constructions.ndjson.gz"
mv "$constructions_tmp/constructions.ndjson.gz" test-data/kernel-reference/constructions.ndjson.gz
