import ansatz.lean.LeanRuntime;
import ansatz.kernel.Name;
import java.util.Arrays;
import java.util.Collections;

/** Packaging/load smoke only; actual prepared frontend acceptance is a separate gate. */
public final class Smoke {
    public static void main(String[] args) {
        Name stringName = LeanRuntime.name("Test.42");
        if (!stringName.isStr() || !"42".equals(stringName.str)) throw new AssertionError("string segment");
        Name numeric = LeanRuntime.structuredName(Arrays.asList("Test.with.dot", 42));
        if (!numeric.isNum() || numeric.num != 42) throw new AssertionError("numeric segment");
        new LeanRuntime.CallSignature(Arrays.asList("unit", Arrays.asList("option", "nat")), "string");
        try {
            LeanRuntime.open(options -> new LeanRuntime.PreparedInput(Collections.emptyMap(), Collections.emptyMap(), new Object()),
                             new LeanRuntime.OpenOptions(Collections.emptyMap()));
            throw new AssertionError("Unchecked provider must reject");
        } catch (LeanRuntime.LeanException expected) {
            if (expected.failure() == null || expected.getCause() == null) throw new AssertionError("failure evidence");
        }
        System.out.println("optional-java-jar-smoke-passed");
    }
}
