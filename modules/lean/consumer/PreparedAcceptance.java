import ansatz.lean.LeanRuntime;
import ansatz.lean.LeanRuntime.*;
import java.math.BigInteger;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

/** Invoke from a host-owned genuinely checked provider scope. No bootstrap is fabricated here. */
public final class PreparedAcceptance {
    public static void verify(PreparedProvider provider, OpenOptions options) {
        AtomicInteger callbacks = new AtomicInteger();
        ExternSpec extern = new ExternSpec("ansatz_facade_host_nat",
            Arrays.asList(new ExternArgument("tobject", false, "nat")), "tobject", "nat",
            values -> { callbacks.incrementAndGet(); return ((BigInteger) values.get(0)).add(BigInteger.ONE); });
        String source = "@[extern \"ansatz_facade_host_nat\"] opaque facadeHost (x : Nat) : Nat := x\n"
            + "def facadeNat (x : Nat) : Nat := facadeHost (facadeHost x)\n"
            + "def facadeString (x : String) : String := x\n";
        SourceRequest request = new SourceRequest(LeanRuntime.name("FacadeAcceptance"),
            Arrays.asList(LeanRuntime.name("facadeNat"), LeanRuntime.name("facadeString")), Initialization.DEFER, "FacadeAcceptance.lean");
        BigInteger large = BigInteger.ONE.shiftLeft(80).add(BigInteger.valueOf(42));
        String unicode = "éλ\u0000😀";
        try (LeanContext base = LeanRuntime.open(provider, options);
             LeanContext branch = base.withExterns(Arrays.asList(extern))) {
            LoadResult loaded = branch.loadString(source, request);
            try (LeanContext compiled = loaded.context()) {
                if (!loaded.success() || loaded.file() == null) throw new AssertionError("source compilation diagnostics");
                try (LeanContext initialized = compiled.initialize(loaded.file())) {
                CallResult nat = initialized.call(loaded.file(), "facadeNat", Arrays.asList(large), new CallSignature(Arrays.asList("nat"), "nat"));
                try (LeanContext afterNat = nat.context()) {
                    if (!large.add(BigInteger.valueOf(2)).equals(nat.value()) || callbacks.get() != 2)
                        throw new AssertionError("exact Nat and two Java SAM invocations");
                    CallResult string = afterNat.call(loaded.file(), "facadeString", Arrays.asList(unicode), new CallSignature(Arrays.asList("string"), "string"));
                    try (LeanContext afterString = string.context(); LeanContext fork = afterString.fork()) {
                        if (!unicode.equals(string.value())) throw new AssertionError("Unicode/NUL String");
                    }
                }
                }
            }
        }
    }
}
