# Original Task.map declarations

Two authentic Lean 4.33.1 CAS declarations: Task.map / lean_task_map and its
original boxed wrapper. Only optional top-level pretty text was removed. The
original-record hashes and the derived fixture hash have distinct meanings;
`provenance.json` pins both against the original producer declaration index.
The wrapper's static FAP closure is the included extern root.

The six raw IR parameters are erased, erased, owned tobject callback, owned object
Task, owned tobject Nat priority, and uint8 sync; the result is object. The four
C inline parameters in lean.h follow type erasure and are not the IR ABI.

The Java implementation selects the native **no-task-manager**, ready-only
branch. It accepts immediate nonnegative Long priorities and canonical Bool
sync 0/1; it rejects heap-sized Nat priorities and pending tasks. This fixture
contains no replacement callback body, fake asynchronous scheduler, pending Task
import, or compatibility claim for the native task-manager branch.

Upstream copyright Microsoft Corporation and contributors,
[Apache 2.0 license](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
Pinned sources: [runtime/object.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp),
[lean.h](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h),
[Init/Core.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Core.lean),
and [ir_interpreter.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp).
