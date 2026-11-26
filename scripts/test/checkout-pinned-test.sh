#!/usr/bin/env bash
# Tests for scripts/lib/checkout-pinned.sh against local git fixtures:
#   bash scripts/test/checkout-pinned-test.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
source "$here/../lib/checkout-pinned.sh"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
fail=0
check() { if eval "$2"; then echo "ok   $1"; else echo "FAIL $1"; fail=1; fi; }

git init -q -b main "$tmp/origin"
g() { git -C "$tmp/origin" -c user.name=t -c user.email=t@t "$@"; }
echo "leanprover/lean4:v1" > "$tmp/origin/lean-toolchain"; g add -A; g commit -qm one; g tag v1
echo "leanprover/lean4:v2" > "$tmp/origin/lean-toolchain"; g commit -qam two; g tag v2
v1=$(g rev-parse v1); v2=$(g rev-parse v2)
git clone -q "$tmp/origin" "$tmp/clone"; c() { git -C "$tmp/clone" "$@"; }

checkout_pinned "$tmp/clone" v1 >/dev/null
check "a tag is checked out detached at its commit" '[ "$(c rev-parse HEAD)" = "$v1" ] && ! c symbolic-ref -q HEAD >/dev/null'
check "an already pinned clone stays" '[ "$(checkout_pinned "$tmp/clone" v1)" = ">>> $tmp/clone is at v1" ]'

echo "hand edit" > "$tmp/clone/lean-toolchain"
check "an edited lean-toolchain is refused, not discarded" '! (checkout_pinned "$tmp/clone" v2 >/dev/null 2>&1) && [ "$(cat "$tmp/clone/lean-toolchain")" = "hand edit" ]'
c checkout -q -- lean-toolchain

c branch -q v3 "$v2"
check "a branch named like a missing tag is not accepted" '! (checkout_pinned "$tmp/clone" v3 >/dev/null 2>&1) && [ "$(c rev-parse HEAD)" = "$v1" ]'

g tag v4 "$v2"
checkout_pinned "$tmp/clone" v4 >/dev/null
check "a tag missing locally is fetched by name" '[ "$(c rev-parse HEAD)" = "$v2" ]'

exit $fail
