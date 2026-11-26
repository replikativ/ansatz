#!/usr/bin/env bash
# Sourced by setup-mathlib.sh; tested by scripts/test/checkout-pinned-test.sh.

# Check out the release TAG `ref` in a clone, detached at the tag's commit, refusing to discard
# uncommitted work. Only the exact ref refs/tags/<ref> is accepted: not a branch of the same
# name, not a revision expression (v1~1), so the store's manifest records the release it says.
checkout_pinned() {
    local dir="$1" ref="$2" oid commit
    if ! git check-ref-format "refs/tags/$ref" || [[ "$ref" == refs/* ]]; then
        echo "ERROR: '$ref' is not a release tag name" >&2
        exit 1
    fi
    if [ -n "$(git -C "$dir" status --porcelain --untracked-files=no)" ]; then
        echo "ERROR: $dir has uncommitted changes; commit or stash them before pinning to $ref" >&2
        if [ "$(basename "$dir")" = "lean4export" ] \
           && [ -n "$(git -C "$dir" status --porcelain --untracked-files=no -- lean-toolchain)" ]; then
            echo "       (earlier versions of this script rewrote lean4export/lean-toolchain; inspect" >&2
            echo "        git -C $dir diff lean-toolchain, and if the edit is not yours:" >&2
            echo "        git -C $dir checkout -- lean-toolchain)" >&2
        fi
        exit 1
    fi
    oid="$(git -C "$dir" show-ref --verify --hash "refs/tags/$ref" 2>/dev/null || true)"
    if [ -z "$oid" ]; then
        # exactly the remote's refs/tags/<ref>, and no other tags (an unrelated moved tag must
        # not fail the fetch)
        if ! git -C "$dir" ls-remote --exit-code --tags origin "refs/tags/$ref" >/dev/null; then
            echo "ERROR: the remote has no tag $ref" >&2
            exit 1
        fi
        git -C "$dir" fetch -q --no-tags origin "refs/tags/$ref:refs/tags/$ref"
        oid="$(git -C "$dir" show-ref --verify --hash "refs/tags/$ref")"
    fi
    commit="$(git -C "$dir" rev-parse --verify "$oid^{commit}")"
    if [ "$(git -C "$dir" rev-parse HEAD)" = "$commit" ] && ! git -C "$dir" symbolic-ref -q HEAD >/dev/null; then
        echo ">>> $dir is at $ref"
    else
        echo ">>> Checking out $ref in $dir"
        git -C "$dir" checkout -q --detach "$commit"
    fi
}
