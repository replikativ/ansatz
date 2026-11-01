# Header-runtime Nat, ready Tasks and checked array reads

This bounded runtime tranche follows Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, preserving exact original
extern ABIs and genuine boxed wrappers. It extends execution coverage without
changing the default prepared-graph grammar or inventing successful panic paths.

## Nat operations

Original Nat.decLe, log2, lor, shiftLeft and shiftRight use logical nonnegative
integers. Small values take Long fast paths; larger values use BigInteger with
the established small-result normalization. Log2(0)=0. OR preserves magnitude
across the small-carrier boundary. All primitive Nat operands remain borrowed;
original wrappers perform their own owned-argument decrements.

Right shift compares its exponent against the base's bit length before any int
narrowing; huge shifts return zero. Zero left-shifted by any valid Nat returns
zero before growth checks. Nonzero left shift validates the result bit length
before allocation, with an explicit limit of 16,777,216 bits. This finite Java
profile can reject allocations that native Lean might attempt. It never wraps
an oversized shift into a signed int or silently changes shift direction.

## Ready Tasks

Task.pure/get have a distinct engine-only ready-Task kind, tag252 and one owning
result field. Pure transfers its input without retaining it. Get retains the
result **before** consuming the Task, matching lean_task_get_own: a unique Task
may hold the final reference to that value. Shared Tasks retain their remaining
aliases; nested ready Tasks use the same ownership rules. Unobserved Task release
releases its result. Fork copies kind and aliases through the existing graph memo.

An arbitrary constructor with the same tag/layout is not a Task. Constructor
projection/mutation/unboxing reject Tasks. No host Future, scheduler, mutex or
native implementation pointer is retained. This supports engine-created ready
values. Ready Task.map now has a [separate continuation gate](JAVA_TASK_MAP.md);
pending tasks, spawn/bind, parallelism and native Task imports remain excluded.
The prepared graph importer does not gain a new Task descriptor incidentally.

## Checked array read valid domain

Original Array.get!Internal and get!InternalBorrowed retain the full four-slot
ABI: erased type, borrowed default, borrowed array, borrowed Nat index. Valid
reads leave the default untouched. The owning getter retains the result; the
borrowed getter does not. Direct external/PAP/imported closure entry into these
borrowed-input primitives requires the proper owning guest wrapper.

Out-of-bounds or huge indices reject before any value retain/decrement with a
named deferred-panic error. Native Lean would acquire a default credit and enter
its configured panic path, whose effects are not yet implemented here. Returning
the default silently would claim unsupported semantics; this profile does not do
that. The borrowed wrapper's result still requires caller lifetime discipline.

## Evidence

The three fixtures contain eighteen exact original rows, including all nine
boxed wrappers: [Nat](../test/fixtures/java-nat-runtime/README.md),
[Task](../test/fixtures/java-task-runtime/README.md), and
[checked arrays](../test/fixtures/java-array-checked-runtime/README.md).
Eight focused tests / 184 assertions pass per driver, covering Nat boundaries,
huge shifts, Task unique/shared/nested/unobserved/fork ownership, kind guards,
checked result ownership and explicit panic rejection. The combined isolated jar
gate passes 450 executions / 15,076 assertions across 53 suites at 384 MiB.
Failed execution retains
the engine's existing ownership-cleanup limitation.

The genuine demand-loaded header probe now reaches Lean.mkEmptyEnvironment,
with eighteen original bodies and 883 IR instructions, in a retained 384 MiB JVM.
Its next missing operation is IO.initializing. That flag requires a source-backed
lifecycle contract, independently from initialized globals/modules; it will not
be replaced with an unexplained constant. This is not complete parsing,
elaboration, kernel admission or frontend self-hosting.
