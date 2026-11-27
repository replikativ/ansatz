# Lean parity corpus

Small, self-contained Lean v4.36.0 files that pin what Lean itself does in the situations the
Ansatz simp and kernel tests assert. Each file under `simp/` names, in its header, the Ansatz test it pairs
with and the result observed with Lean v4.36.0 (core only, no Mathlib), and asserts that result:
an `example` that only elaborates when simp produces the expected form, `fail_if_success` for a
rewrite that must not happen, or `#guard_msgs` for an expected error or warning.

Files under `kernel/` pin the kernel's inductive admission (`environment::add_inductive`): they
submit declarations through the elaborator or, to reach the kernel directly, through `addDecl`,
and pair with `test/ansatz/kernel_inductive_admission_test.clj`.

`ParitySimpSets.lean` declares the custom simp sets the `q5_*` files use (`register_simp_attr`
must live in an imported module); `run.sh` compiles it first.

Run all files (fails on any error or `#guard_msgs` mismatch):

    test/lean-parity/run.sh            # LEAN=/path/to/lean to override the toolchain

CI has no Lean toolchain; run this when changing simp behaviour the corpus covers, and add a file
when an Ansatz test encodes a claim about Lean's behaviour.
