"""Recognize both root and nested Pattern namespace resources/classes."""


def entries(names):
    return {name for name in names if not name.endswith('/') and
            (name.startswith('pattern/') or name in {'pattern.clj', 'pattern.cljc', 'pattern.cljs', 'pattern__init.class'}
             or (name.startswith('pattern$') and name.endswith('.class')))}
