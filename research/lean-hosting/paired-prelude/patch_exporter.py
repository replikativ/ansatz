#!/usr/bin/env python3
"""Patch a copied pinned exporter; upstream remains strictly read-only.

Expr's default BEq is alpha equivalence. Producer DAG/cache identities must use
ExprStructEq/Expr.equal to retain binder names and BinderInfo. This changes cache
keys only; MData erasure and let.nonDep normalization remain explicit policies.
"""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

UPSTREAM_SHA256 = '1c60d571dc24bfb99e7cbb218d8d489919bbc871238f6db9c76248521fbea998'
PATCHED_SHA256 = 'e77e2ab2f85e39eed95779b92b90837edf807e14aadffeb7569ef85015e8805f'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify(upstream, patched):
    if digest(upstream) != UPSTREAM_SHA256:
        raise ValueError('unexpected upstream Export.lean bytes; refusing patch')
    if digest(patched) != PATCHED_SHA256:
        raise ValueError('unexpected structurally keyed Export.lean bytes')


def apply(upstream, destination):
    upstream, destination = Path(upstream), Path(destination)
    if upstream.resolve() == destination.resolve():
        raise ValueError('upstream exporter must remain read-only')
    if digest(upstream) != UPSTREAM_SHA256:
        raise ValueError('unexpected upstream Export.lean bytes; refusing patch')
    destination.parent.mkdir(parents=True, exist_ok=True)
    patch = Path(__file__).with_name('exporter-structural-cache.patch')
    with tempfile.TemporaryDirectory(prefix='patch-exporter-', dir=destination.parent) as stage:
        candidate = Path(stage) / 'Export.lean'
        subprocess.run(['patch', '--batch', '--fuzz=0', '--no-backup-if-mismatch',
                        '--output', str(candidate), str(upstream), str(patch)], check=True)
        verify(upstream, candidate)
        candidate.replace(destination)


if __name__ == '__main__':
    apply(*sys.argv[1:])
