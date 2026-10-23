# Lean/JVM release research, 2026-10-23

Research supporting a future Ansatz release with hosted Lean. None of the
proposed offering below is a shipped-product or production-readiness claim.
Recheck upstream facts before publication. Continue implementation using the
[campaign plan](CAMPAIGN_CONTINUATION_2026-10-23.md).

## Potential offering

Two distinct support tiers are useful:

1. Embed executable Lean domain models in conventional Clojure/Ansatz systems,
   retaining Lean specifications/proofs while JVM libraries handle external IO.
2. Host broader Lean programs with JVM deployment, observability and interop.

Prioritize embedding. Running the same Lean implementation can avoid maintaining
a second hand-written model implementation, but introduces our own lowering,
runtime, primitive and interop correctness boundary. Kernel compatibility does
not prove that boundary correct. Pure proofs also do not verify arbitrary host
effects, transaction protocols or resource management.

Keep the user's goals: git-like persistent application memory, cheap retained
forks, REPL-grounded experimentation, dynamic staging and selective compilation.
The near-term goal is Lean integration with the existing replikativ stack, not a
wholesale Clojure-to-Lean port. Whole-heap/process replay, external effects and
durable code identity remain distinct problems from immutable value sharing.

## What production examples actually establish

- [Cedar's authors](https://bhaktishh.github.io/papers/how-we-built-cedar.pdf)
  explain their 2024 decision to use a Lean executable model and Rust production
  implementation. Reasons include developer/library availability, debugging
  generated C and handwritten/native interactions, and compiler trust. They use
  differential random testing, not a proof of Rust/model equivalence. They do
  not cite RC cycles as the reason. Their differential-testing medians of 6 us
  for the Lean authorizer and 10 us for Rust are workload-specific, not a general
  language comparison. Current tooling may differ from their 2024 assessment.
- [Verso](https://verso.lean-lang.org/) is actually implemented in Lean. It is a
  document/static-site generator; the
  [website repository](https://github.com/leanprover/verso-website) documents Lean
  generation of static files and automatic deployment. This is genuine used
  software, not a rejection of Lean runtime hosting, but not evidence for a
  long-running mutable application server.
- [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/),
  the compiler and language server establish substantial developer-tool usage.
- [TodoMVC Max](https://github.com/paulbutcher/lean-todomvc-max) demonstrates a
  broader app stack and AWS deployment configuration. We did not verify a named
  production customer/service operating it. Do not call deployment instructions
  evidence of an established deployment. Frameworks such as LeanTEA and Qed
  likewise do not establish operator experience by their existence alone.
- This investigation did not verify a conventional CRUD/SaaS production service
  primarily implemented in Lean. That is a limit of the public evidence found,
  not proof that no such private/public deployment exists.

Practical implication: ecosystem/tooling concerns are documented. We do not have
good incident-frequency data for long-running Lean application services; absence
of reported leaks is not evidence of broad operational experience.

## Reference counting and ordinary IO cycles

The [Lean reference manual](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/)
describes RC without cycle collection and qualifies acyclicity to the verifiable
fragment. Ordinary IO can construct a cell containing a closure that captures
that same cell, without an `unsafe` declaration. Do not describe all accepted
Lean code as cycle-free by construction.

A native reproduction on Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Linux C backend, established:

- 1,000 acyclic external finalizer witnesses were all finalized.
- 1,000 explicitly broken cycles were all finalized.
- 1,000 abandoned cycles remained live while subsequent acyclic witnesses were
  finalized normally. A held cycle became finalizable after explicit breaking.
- A separate builtin-only IO.Ref/closure/ByteArray experiment used no custom
  externs or unsafe declarations. Its acyclic and broken controls stabilized
  near 18 MiB RSS; the cyclic case rose to about 65 MiB after 32 one-MiB payloads.
  RSS is corroboration, not exact leaked-byte accounting.

The deterministic witness uses trusted observation FFI; the ordinary workload
does not use unsafe declarations. The builtin-only corroboration avoids that
custom instrumentation. This is a leak-freedom finding, not kernel unsoundness,
use-after-free, or a claim about all Lean versions/backends or incident frequency.

Original report SHA-256:
`99f2839933b0148aa14593c7152f3e725bf06abcf0cb85f627a39216127716df`.
Original manifest SHA-256:
`30fb8440c696277d32fc67d7043d0f193120953cf0b31b004427c12b44e1de34`.
The complete reproduction is retained in this worktree's local
`target/artifact-contract/lean-production-research-20261023/rc-reproduction/`.
Its report includes the source, commands, generated C, observed outputs and
resource receipts. The manifest authenticates 34 original files. This local
artifact is not a published release asset; preserve or publish a reviewed
portable source reproduction before referring release readers to it.

The [January 2026 upstream discussion](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lean%27s.20Reference.20Counting.20and.20Cycle.20and.20Unsafe.html)
assigns cycle breaking to the programmer for its unsafe example. That statement
does not itself analyze the ordinary IO closure case we reproduced.

The [HTTP task retention report #14918](https://github.com/leanprover/lean4/issues/14918)
is an additional practical report, not our reproduction and not an established
RC-cycle diagnosis. Do not claim tracing GC fixes it without confirming its
actual retention roots. Snapshot histories and registries can retain state with
either RC or tracing GC.

## Consequences for our runtime and release language

JVM tracing GC can collect an otherwise unreachable equivalent JVM object cycle.
It cannot collect guest objects still reachable through a live World heap map,
registry, checkpoint, native owner or code cache. Our current runtime models RC;
hosting it on a GC does not by itself establish guest cycle collection.

Specify which observations of RC/uniqueness are supported, when ownership is
emulated, and how guest objects become unreachable from host roots. Verify
repeated edit/close workloads, retained-version bounds, callbacks and failure
packets before promising improved leak behavior. Native resources still require
explicit lifetimes, regardless of object collection.

The release should make debugging/source mapping, explicit capabilities, reliable
packaging and observability concrete acceptance criteria. Explain supported
modules and IO instead of claiming arbitrary Lean FFI or full production Lean.
The research supports a potential benefit; implementation and operator evidence
must support any eventual maturity claim.
