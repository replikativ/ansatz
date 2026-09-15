#!/bin/bash
# Publish an imported store as a GitHub release of the store repository.
#
#   ./scripts/publish-store.sh <store-dir> [revision]
#
# Packs the store (ansatz.store.pack) into ~/.cache/ansatz-store-artifacts/<id>/, creates the
# release <id> in $ANSATZ_STORE_REPO (default replikativ/ansatz-stores) with the parts and the
# descriptor, and prints the index entry to commit to that repository's stores.edn — which is
# what makes the new import reachable: ansatz reads the index at fetch time, so publishing an
# import needs no ansatz release.
#
# A store id is <name>-<library tag>-f<store format>, plus -r<n> when the same library and
# format are imported again (our importer changed).
set -euo pipefail
cd "$(dirname "$0")/.."

STORE_DIR="${1:?usage: publish-store.sh <store-dir> [revision]}"
REVISION="${2:-}"
REPO="${ANSATZ_STORE_REPO:-replikativ/ansatz-stores}"
OUT="${ANSATZ_STORE_ARTIFACTS:-$HOME/.cache/ansatz-store-artifacts}"

echo ">>> Packing $STORE_DIR"
ID=$(clojure -M -e "(require '[ansatz.store.pack :as p]) (print (p/store-id \"$STORE_DIR\" ${REVISION:-nil}))")
clojure -M -m ansatz.store.pack "$STORE_DIR" "$OUT" "$ID"
DIR="$OUT/$ID"

echo ""
echo ">>> Publishing $ID to $REPO"
if gh release view "$ID" --repo "$REPO" >/dev/null 2>&1; then
    echo "!!! release $ID already exists — a published store is immutable."
    echo "    Re-import with a revision: ./scripts/publish-store.sh $STORE_DIR <n>"
    exit 1
fi
gh release create "$ID" --repo "$REPO" \
   --title "$ID" \
   --notes "$(printf 'Store artifacts for `%s`.\n\nFetched by `(ansatz.core/init! "%s")`; see the repository README.\n\n```clojure\n%s```\n' \
              "$ID" "$(basename "$STORE_DIR")" "$(cat "$DIR/store.edn")")" \
   "$DIR"/*.tar.gz "$DIR/store.edn"

echo ""
echo ">>> Commit this to $REPO stores.edn (under :stores), then it is live:"
cat "$DIR/index-entry.edn"
