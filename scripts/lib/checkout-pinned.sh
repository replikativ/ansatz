#!/usr/bin/env bash
# Sourced by setup-mathlib.sh; tested by scripts/test/checkout-pinned-test.sh.

# Check out the release TAG `ref` in a clone (detached at the tag's commit), refusing to
# discard uncommitted work. Only refs/tags/<ref> is accepted, so a branch of the same name can
# never stand in for the release the manifest records.
checkout_pinned() {
    local dir="$1" ref="$2" commit
    if [ -n "$(git -C "$dir" status --porcelain --untracked-files=no)" ]; then
        echo "ERROR: $dir has uncommitted changes; commit or stash them before pinning to $ref" >&2
        if [ -n "$(git -C "$dir" status --porcelain --untracked-files=no -- lean-toolchain)" ]; then
            echo "       (earlier versions of this script rewrote lean-toolchain; if that edit is not" >&2
            echo "        yours: git -C $dir checkout -- lean-toolchain)" >&2
        fi
        exit 1
    fi
    commit="$(git -C "$dir" rev-parse -q --verify "refs/tags/$ref^{commit}" || true)"
    if [ -z "$commit" ]; then
        git -C "$dir" fetch -q origin "refs/tags/$ref:refs/tags/$ref"
        commit="$(git -C "$dir" rev-parse -q --verify "refs/tags/$ref^{commit}")"
    fi
    if [ "$(git -C "$dir" rev-parse HEAD)" = "$commit" ]; then
        echo ">>> $dir is at $ref"
    else
        echo ">>> Checking out $ref in $dir"
        git -C "$dir" checkout -q --detach "$commit"
    fi
}
