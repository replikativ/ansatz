# Genuine source loading into the Java application tier

The [recorded run](../measurements/genuine-java-pure-provider-2026-10-28.edn)
used a fresh source/class cohort from commit
`5f84038d97eb7b79c657b0221e75347976e887b0`. The hosted Lean frontend loaded
the original [GraphChainA source](java-ir-baseline/GraphChainA.lean), admitted its
definitions through the existing Java kernel path, and selected the new private
Java application tier for five calls. No native per-file compiler was invoked.

The observations cover:

- Original Nat identity on `184467440737095516160000`.
- String identity with supplementary Unicode, NUL and newline.
- An edited Nat definition returning `7` from a separately loaded version.
- A call through the retained original version returning `41`.
- The edited version's unchanged String identity.

Every call recorded Java selection and completion. The source/boxed ABI,
original admitted rows and logical Nat/String signature were checked by the
[pure provider adapter](JAVA_PURE_PROVIDER.md). Seven returned experiment
contexts were explicitly closed. This is genuine source evidence beyond the
raw-IR fixtures, within the narrow acyclic no-extern application profile.

## Retained provider and lifecycle

The provider freshly checked 65,994 Init declarations, prepared helpers and the
Init prefix, then remained resident through the source experiments. The same
provider subsequently completed all seventeen existing controller stages,
including A/B/A sources, callbacks and disposal. Every tracked controller Context
and the native Source lease closed before the large JVM exited with status zero.

The driver ran the reviewed developer staging operations `initialize!` and
`continue!`. This is not a run through the bootstrap's terminal launch entrypoint
or an isolated public Java SDK consumer; the receipt distinguishes those facts.
The actual Java engine artifact is pinned independently from the Clojure/kernel
cohort. Later eager-fork changes have their separate bounded artifact gate.

Preparation restored in 89.3 s and checked Init in 180.7 s. Guarded peak
process-group RSS was 3.46 GiB with a 3 GiB maximum heap. The guard's 25-minute
elapsed duration includes interactive REPL work and subsequent experiments; it
is not a startup benchmark. Caller-thread strict-check allocation was about
239.5 GB cumulatively, not retained heap. The
[bootstrap profile review](JAVA_BOOTSTRAP_PROFILES.md) separates this audit cost
from a proposed trusted-artifact startup profile.

## DSL observation and limit

The actual checked Env resolved through protected guest helpers also supported
an Ansatz lambda referencing `GraphChainA.nat`; the kernel inferred Nat and
reduced its application to 42. This probe explicitly installed an empty instance
registry on an immutable metadata overlay and used an instance-free lambda.
It did not import Lean's instance or simp metadata.

Without that explicit DSL setup, elaboration failed with `no instance registry`.
The remaining bridge needs a version-bound metadata view, not a substituted
bundled registry. Native priorities, active scopes, erasures and simp phases
matter. Logical declaration publication and callable compiled-code publication
also remain distinct. No bidirectional theorem/definition SDK is claimed here.

## Reproduction boundary

`java-ir-baseline/genuine-provider.clj` contains definitions only. Its `run!`
accepts a borrowed, live, freshly checked resident provider, an isolated Java
class basis and the exact original fixture text. It never bootstraps on load;
it escrows returned owners before assertions, does not retry failures, and
provides explicit successful-child cleanup. The provider lease must outlive all
descendants and retained failures.

The ignored staging pack binds the immutable source/class inventory, dependency
basis, original producer artifacts and attachment hashes. Small CI tests do not
replay its expensive checking run. Broader IR selection, metadata/publication,
project examples and clean public-package acceptance remain release work.
