# Worker guide (read before your task brief)

You are one of several agents improving the ansatz tactic layer under `docs/QUALITY_PLAN.md`.
A coordinator dispatches the tasks, reviews every diff against the Lean source, and merges.
Your task brief (`docs/quality/tasks/<ID>.md`) states the goal, the scope fence and the acceptance.

## Environment
- You work in your own git worktree on branch `quality/<ID>`. Commit there. Do not push, do
  not `git stash`, and do not touch other worktrees or `~/Development/ansatz` itself.
- The Lean 4 reference source is `/home/christian-weilbach/Development/lean4`
  (`src/Lean/Meta/Tactic/...`, `src/Lean/Elab/Tactic/...`, `src/Init/...`). Read the Lean
  implementation **before** you implement, and port it faithfully. In comments, cite the Lean
  file and function you followed.
- A Lean toolchain for checking `.lean` reference files (no Mathlib):
  `~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean FILE.lean` (exit 0 + no output = OK).
- Project rules are in `CLAUDE.md` at the repo root. They apply to you too.

## JVM / REPL (shared machine: memory is the bottleneck)
- Start a JVM **only** through the slot script, on the port your brief assigns:
  `scripts/jvm-slot.sh repl <PORT> "<ID> worker"`. It waits for a free slot (max 3 machine-wide)
  and starts an nREPL at `-Xmx1g` in your worktree.
- Evaluate with `clj-nrepl-eval -p <PORT> --timeout 600000 "<code>"`. Reload changed namespaces
  with `(require 'ns :reload)`. After reloading `ansatz.core`, also run
  `(reset! ansatz.core/tactic-registry @#'ansatz.core/builtin-tactics)`: the registry is a
  `defonce`, and without this the old tactic closures stay active.
- Run only the test namespaces your brief names, in the REPL:
  `(binding [clojure.test/*test-out* *out*] (clojure.test/run-tests 'ns1 'ns2))`. Write long
  output to a file and grep it; don't rerun to grep.
- **Never** run the full suite (`clj -M:test`), never use `-Xmx` above 1g, never start a JVM
  outside the slot script, never kill a process you did not start. The coordinator runs the full
  suite at merge time.
- When you are done (or blocked), stop your REPL: `scripts/jvm-slot.sh stop <PORT>`.
- Java sources (`src-java`) need `clj -J-Xmx1g -T:build javac` after a change, run while you hold
  your slot (stop the REPL first, then restart it).

## Engineering rules
- **Fail loudly.** A tactic that does not apply throws
  `(ex-info "Tactic error: …" {:kind :tactic-error …})`. Catch only those (`ExceptionInfo` with
  `:kind :tactic-error`) where "not applicable" is a legitimate outcome. Never catch `Exception`,
  `Throwable`, `RuntimeException`, NPE, ClassCast or StackOverflow to mean "no progress". Add no
  new broad catch. If you find a bug that a broad catch was hiding, fix it, or record it in your
  result if it is outside your scope.
- **Lean semantics first.** Where ansatz must deviate (the surface encoding compiles `if` to
  `Bool.rec`, comparisons to `Nat.ble`/`Nat.beq`), keep the deviation minimal and explain it in a
  comment.
- **No silent caps.** A limit either raises a tactic error naming the limit, or is Lean's limit.
- Match the surrounding code style. Keep comments as dense as the surrounding code, not denser.
- Kernel soundness is not yours to weaken: never bypass `check-constant`, and never accept a
  proof the kernel rejects.

## Deliverable
End with a result file `docs/quality/results/<ID>.md` in your worktree, committed, containing:
1. What changed (files, functions) and which Lean code it follows.
2. The exact test namespaces you ran and their summary lines (`Ran N tests … F failures`).
3. Bugs your changes revealed (fixed or not), with file:line.
4. Open issues and anything you were unsure about. Say "unverified" where you did not check.
