# UInt64 scalar arithmetic family

This tranche adds thirteen exact original extern ABIs: `Bool.toUInt64`, and
`UInt64.add`, `sub`, `mul`, `div`, `mod`, `land`, `lor`, `complement`, `neg`,
`log2`, `shiftLeft`, and `decLe`. It completes the arithmetic/logical group around
the existing UInt64 lane operations. It introduces no lane, Node field, object
copy, asynchronous work or arithmetic Node representation.

The reached original `_private.Lean.Meta.Basic.0.Lean.Meta.Config.toKey` body
(SHA256 `82d5b3a5de8fa59ac234d22a61c52b62ea533cb1b4370a66099a6e35576f93ae`)
uses authentic enum-to-UInt64 guest functions plus Bool conversion, shifts and
bitwise OR. The enum implementations and their ABI remain original guest IR.
`UInt64.pow` is also an original guest fdecl, not a native scalar primitive;
this tranche does not substitute a new exponentiation algorithm or bind a
nonexistent native pow symbol. Additional conversions and UInt16 remain outside
this tranche. Existing UInt64 conversions, Float and other lane behavior remain.

Source authority is Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`src/include/lean/lean.h` (UInt64 block and Bool conversion), and
`src/Init/Data/UInt/Basic.lean`. Arithmetic wraps modulo 2^64. Comparisons,
division and remainder are unsigned; division by zero returns zero and remainder
by zero returns the dividend. Shift distances reduce modulo64. Complement and
negation preserve raw bits; log2 returns floor(log2 n), including zero for n=0.
Java long arithmetic, unsigned division/remainder/comparison and low-six-bit
shift masking implement these fixed64 semantics. Public values remain exact
nonnegative Long/BigInteger values bounded by 2^64−1, while internal transport
retains raw signed-long bits. No implicit UInt64/USize lane coercion is added.

The source Bool domain is canonical zero or one. Public raw root Bool conversion
rejects other UInt8 values before frame ownership claims; static FAP execution checks the same domain. Public scalar
partial targets require original boxed wrappers. Malformed Bool data reaching
conversion inside such a wrapper fails after legitimate wrapper/AP entry;
no preclaim rejection is claimed for that guest failure. This deliberately rejects malformed
Bool representations rather than claiming the C inline cast defines new Bool
values. Genuine valid boxed Bool conversion executes its original wrapper.

New intrinsic IDs are selected by an explicit family predicate. Dispatch does not
assume the new IDs are contiguous with the older UInt64 or USize entries. Both
recursive and explicit engines use the same arithmetic implementation. No owner
credit belongs to a raw scalar result. Original boxed wrappers retain their
ordinary allocations/releases, and partial applications own their captured boxes.

The fixture `test/fixtures/java-u64-scalars-runtime/` contains 26 original root/
boxed rows with full original CAS identities, plus five original Config/enum rows.
Only optional top-level pretty text is omitted; raw Names, ABI, bodies and source
metadata remain. The Config body test uses explicitly modeled scalar storage;
it is not an actual frontend result or an imported configuration capability.

`pinned-inline.h` copies exactly thirteen pinned Lean inline bodies, with original
attribution/license and only minimal include scaffolding. `run-oracle.py` verifies
the complete upstream header SHA and exact body extraction, compiles a bounded
native driver and reads test vectors at runtime. The native run succeeded for
40 vectors ×13 functions with empty stderr under a 256 MiB address-space cap.
This is a compiled pinned inline arithmetic oracle, not a full Lean runtime ABI
oracle, checkpoint producer identity proof, JVM benchmark or frontend claim.

The root compiled frozen Java source SHA256
`01774fd4a28b6bf00e2ad9dbae8ec61f47d334557421eb80b44ca43868933081`
for Java 11 and ran the focused suite in its retained 384 MiB REPL. Both recursive
and explicit modes passed six tests / 1,634 assertions each (zero failures/errors).
The source review found the arithmetic and dispatcher consistent with the pinned
native evidence. The completed isolated jar gate passed 96 suites / 943 tests / 49,995 assertions
with exit 0 and a 384 MiB heap limit. Its jar SHA256 is
`e60f3a18be637fa57529e237d3500a6603ac3970f4306180e58a4ac4800c7d45`.
This feature worker launched no JVM.
