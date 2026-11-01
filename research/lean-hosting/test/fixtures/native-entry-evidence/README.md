# Native entry evidence source fixtures

These source fixtures passed the coordinated native evidence gate. No JVM was
launched and this is not a Java execution or Java type-checking receipt. The
package's `entry-evidence-validation.json` records the actual phase results.

Under the coordinated native process/resource guard, compile NativeEntryCases
with the pinned official compiler into a private build directory. Invoke the
separate `lean-native-entry-evidence --entries requests.json` with that directory
on LEAN_PATH. Build the tool explicitly with `scripts/build-entry-evidence.sh`;
it does not replace the accepted exporter. Inspect actual raw/boxed choices,
especially stringCase's observed borrow bits, without assuming an optimization.
Compile NativeEntryImported after NativeEntryCases and use imported-requests.json
to exercise imported aliases and actual base-module boxed lookup. Compile
NativeEntryInitCases to exercise named and anonymous regular/builtin IO Unit
initializer detection. Its ordinary entry permits the original attribute
inventory to be inspected without admitting an initializer as a callable entry.

Positive requests cover Nat, a reducible type alias, String, actual IO Unit and a
literal numeric-looking string Name. For negatives, copy the request document
into private output and replace one entry with polymorphic, unsafeIdentity,
partialLoop, noBody, proofOnly, an absent Name, a wrong signature or numeric Name
component 7. Each must fail before a successful evidence object is printed.
Do not infer a passing gate from the JSON shape or source-reading review.

The actual partialLoop negative is important: its public CI is opaque and not
marked `isPartial`; the original compiler's `declIsNotUnsafe` detects its actual
partial implementation. Fourteen negative requests included all four original
IO Unit initializer names (two generated anonymous actions).

The code's source phase must also be exported through unchanged Export.lean so
the build manifest can bind source/olean/local IR/initialization-plan receipts
to the new evidence tool, request and output hashes. A post-import `.olean` view
does not recover original local initialization order.
