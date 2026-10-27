# Finite mutable frontend and JVM application slice

Status: the finite genuine gate passed on main `01016b2`, including restoration,
fresh checking, hosted A/B files, selected JVM execution, a Clojure callback and
managed disposal. Exact evidence and measured limits are recorded below. Broad
Lean compatibility and efficient loading remain separate, unproven goals.

The profile is `ansatz-producer50f-coherent-jvm-application-consumer/1`; its contract
schema is `ansatz-coherent-jvm-application-contract/1`. Original producer recipe,
checkpoint format, kernel policy and historical frontend consumer profile remain
unchanged. The factory is identity-issued through the new explicit
`make-coherent-jvm-application-factory` constructor. Restore checks exact producer,
consumer, profile and contract identities. Preparation dispatches the actual
Factory profile, without inventing a Project stage for direct resident files.

The serialized application policy is a closed `:composition/:application` map:

- `:execution-roles`: frontend mutable and application JVM, each fuel500,000,000
  and compile threshold1. Java checker fuel is a separate original policy field.
- `:transition`: exactly `[:mutable :jvm]`.
- `:selection-limits`:16 functions,64 descriptors,100,000 fact/preflight work and
 16KiB source files. Existing typed preparation has its separate bounded pass.
- `:corpus`:1–4 rows, each with distinct A/B direct-input IDs, module/entry/worker
  Lean Names, scalar codecs,1–4 explicit calls with A/B expectations and an
  independent ordinary fallback entry. All capture IDs are globally distinct.
- `:callback`: one explicit exact boxed String-to-Nat ABI, argument ownership,
  entry, bounded input, expected UTF-8 byte length and `:utf8-length` controller
  implementation. This belongs to the first corpus row. No serialized host fn.

The exact stage program is:

```clojure
[:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio
 :cases-on :seal :helper-value :init-prefix
 :load-a :select-a :call-a :callback :load-b :select-b :call-b-a :dispose]
```

`construct!` authenticates inputs and composition only; it acquires no Source and
performs no guest execution/checking. `run!` restores and strictly checks once,
prepares helpers through the existing public controller, initializes the required
emitted helper value once, then builds an independently authorized callback and
pristine Init prefix. Classic implicit Init imports must match that real prefix.
`:defer` is accepted only when the actual admitted initialization plan is empty;
required initialization is an explicit unresolved prerequisite.

Both A and B load on the retained pristine mutable context. Each loaded World is
reopened through public `raw/open-functions` and `resident/adopt-prepared`, under
THE ORIGINAL independent trusted configuration and exact binding objects. The
controller never reconstructs authority from the live executable image. One
explicit code-cache capability is shared by all A/B JVM branches. The public
resident compiler setter changes selection in a new branch and preserves input.

Selection reads the actual admitted worker row first, then only demanded
callee/extern rows from the original catalogue. Bounded facts use M1/M2 and the
real Pattern representation pass; exact installed bodies/wrappers are checked.
No all-Init scan, name-based SUM recognition, protected replacement or new engine
is used. Unsupported worker shapes refuse selected acceptance; they do not become
successful compiled evidence merely because generic execution works.

Boxed calls record actual typed-tail artifact identity AND executor return
`:specialized`. The fallback control runs on the selected JVM context with no
selected-worker events. The typed callback receives immutable values and performs
exactly one effect; this is not nested guest reentry. Loading A/B may not add
callback effects. B must have different source, admitted unit and worker/compiler
keys. A/B/A keeps old A callable; a newly selected old-A program must hit the same
shared cache and execute the same artifact. A wrong-image handle rejects before
encoding, and any unexpected returned owner is still escrowed before failure.

Every Context/prefix result is captured before postconditions, timings or logs.
Known temporary call contexts close after observation; retained version contexts
close in reverse order. Each inherited Init-prefix registry is released through
its existing public capability before its Context closes. Source lease closure
comes last and checks the actual Store's closed flag. Unknown partial operation
or destructive cleanup failure retains canonical escrow and lease; no retry,
rollback fiction or disposal success is synthesized.

Final result top keys are exactly status/disposal/stages, contract/implementation/
profile identities, the frontend execution triple, separate application execution
and `:measurements`. Measurements contain only bounded `:corpus`, `:callback` and
`:phases` scalar data. They retain no World, Context, lease or checking authority.
The17 phase entries use `:stage` in exact order. Restore and strict checking are
separate segments under fresh-init. Shared helper preparation timing is recorded
once and labelled for its other stages; overlapping spans are not summed.
Bounded running messages precede operations. The launcher's new-profile outer
error boundary must print only bounded class/message data, never giant ex-data.

The component [validation record](../measurements/coherent-jvm-slice-components.json)
separates new models, historical source-pin checks and native/data prerequisites.
A fresh source/class/dependency capture, 24-source Java compilation, resource
preflight and genuine A/B load/selected-call/callback/disposal gate subsequently
passed, as recorded below. General Project dependency reload, Mcmc sampling, broader non-tail JIT,
Java facade composition and production deployment are separate gates.


## Current-main genuine acceptance, 2026-10-27

The exact current-main cohort at `01016b20c425b059331b1649abbd5e72170178f7`
passed the full seventeen-stage gate in one fresh JVM. Source-level `entry` and
`identity64` names resolved through admitted manifest boxed targets. Actual hosted
A/B elaboration, the selected worker, String-to-Nat Clojure callback, A/B/A
isolation, shared-cache reuse, wrong-image rejection before encoding, and managed
Context/prefix/Source disposal all passed. This is finite fixture coverage,
not complete Lean/Mathlib compatibility or packaged Java-facade acceptance.

[The receipt](../measurements/genuine-hosted-jvm-main01016.json) and
[verbatim output](../measurements/genuine-hosted-jvm-main01016.stdout) preserve the
exact cohort, launch, limits, phase events and terminal result. Detailed private
corpus results were not printed; value/route/cache statements are supported by
the authenticated controller's mandatory assertions, not reconstructed raw keys.

| Operation | Inclusive wall time |
| --- | ---: |
| Restore checkpoint | 292.15 s |
| Bootstrap support plus fresh strict Init checking/projection/association | 655.81 s |
| Prepare Init prefix | 17.05 s |
| Load A | 50.54 s |
| Select A compiler facts/context | 1.08 s |
| A calls: three selected plus one generic fallback | 2.86 s |
| One Clojure callback | 0.47 s |
| Load B from pristine baseline | 43.94 s |
| Select B | 0.71 s |
| B/A calls plus version/cache controls | 2.87 s |
| Managed disposal | 2.95 s |

The complete guarded process took 1110.34 s, peaked at 3,637,760,000 bytes group
RSS, and kept at least 1,734,909,952 bytes host memory available. Its heap cap was
3 GiB and group RSS cap 4 GiB. G1 used two parallel and one concurrent worker;
no full collection occurred. A preceding Serial attempt restored successfully
but was deliberately stopped with strict checking incomplete after sustained
full-GC pressure. This supports investigating generation layout; it is not a
controlled collector throughput comparison or proof of the minimum heap.

Phase CPU/allocation counters measure the caller thread. Restore delegates work,
so its reported 6 ms CPU/102 KB excludes the restore worker and must not be
interpreted as total restore work. Shared helper preparation spans overlap and
must be counted once. Call phases include validation, codecs, Context retirement
and version controls; they are not primitive-worker throughput benchmarks.

Loading and public-call latency still need substantial improvement. Profile
those boundaries and reuse validated immutable-image facts before attributing
the cost to interpretation. A direct resident load is different from Project
publication/graph loading. Next compatibility gates should expand to unchanged
programs and imports, keeping proof-only/noncomputable modules separate from
executable roots. The unchanged rbmap/Mcmc constructor runtime corpus is prior
native-exported IR evidence; this new hosted-source gate does not turn that
whole corpus into hosted-file acceptance.
