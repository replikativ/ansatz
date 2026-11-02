import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import java.math.BigInteger;
import java.util.*;

/** Genuine native-source-built scalar/buffer/choice corpus, executed JVM-only. */
public final class ScalarInteropSmoke {
    private static int checks;
    private static void check(boolean ok) { checks++; if (!ok) throw new AssertionError("check " + checks); }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static void refuse(String code, Runnable action) {
        try { action.run(); throw new AssertionError("Expected " + code); }
        catch (LeanException error) { check(code.equals(error.code())); }
    }
    public static void main(String[] args) throws Exception {
        try (Lean runtime = Lean.open();
             LeanProject p = runtime.loadArtifact(ScalarInteropSmoke.class.getClassLoader(), "lean/scalar-interop.zip",
                 "a0d7543e47caacc14cfbaf04237c22c7219ab9a38a8906a1dfe2c0d599b65dfc")) {
            check(p.call("extByte", 255L).equals(n(0)));
            check(p.call("extSigned", 42L).equals(n(-42)));
            check(p.call("extSigned", Long.MIN_VALUE).equals(n(Long.MIN_VALUE)));
            check(p.call("extDouble", 1.25).equals(1.75));
            check(p.call("extSingle", Float.valueOf(16777216f)).equals(Float.valueOf(16777216f)));
            check(Double.isInfinite((Double) p.call("extDouble", Double.POSITIVE_INFINITY)));
            check(Float.isNaN((Float) p.call("extSingle", Float.NaN)));
            check(p.call("extChar", 0x1f600).equals(Integer.valueOf(0x1f600)));
            check(p.call("extWord", 41L).equals(n(42)));
            check(p.call("extConstantByte").equals(n(255)));
            check(p.call("extConstantFloat").equals(1.5));
            check(p.call("extArray", List.of(1L, 2L)).equals(List.of(n(1), n(2))));
            check(p.call("extArrayPush", List.of(1L, 2L), 3L).equals(List.of(n(1), n(2), n(3))));
            byte[] input = new byte[]{0, -1};
            byte[] copy = (byte[]) p.call("extBytes", input); input[0] = 9;
            check(Arrays.equals(copy, new byte[]{0, -1}));
            check(Arrays.equals((byte[]) p.call("extBytesPush", new byte[]{0, -1}, 42L), new byte[]{0, -1, 42}));
            LeanChoice sum = (LeanChoice) p.call("extSum", LeanChoice.left(true));
            check(!sum.isLeft() && sum.value().equals(true));
            LeanChoice sum2 = (LeanChoice) p.call("extSum", LeanChoice.right(42L));
            check(sum2.isLeft() && sum2.value().equals(n(42)));
            LeanChoice error = (LeanChoice) p.call("extExcept", LeanChoice.left("error"));
            LeanChoice ok = (LeanChoice) p.call("extExcept", LeanChoice.right(42L));
            check(error.isLeft() && error.value().equals("error"));
            check(!ok.isLeft() && ok.value().equals(n(42)));
            List<?> machines = List.of(n(65535), List.of(new BigInteger("4294967295"),
                List.of(n(-128), List.of(n(-32768), List.of(n(-2147483648L),
                    List.of(new BigInteger("18446744073709551615"), n(-1)))))));
            check(p.call("extOtherMachines", machines).equals(machines));
            refuse("InvalidArgument", () -> p.call("extByte", -1L));
            refuse("InvalidArgument", () -> p.call("extByte", 256L));
            refuse("InvalidArgument", () -> p.call("extSigned", BigInteger.ONE.shiftLeft(63)));
            refuse("InvalidArgument", () -> p.call("extChar", 0xd800));
            refuse("InvalidArgument", () -> p.call("extChar", 0x110000));
            refuse("UnsupportedArgumentType", () -> p.call("extSingle", Double.valueOf(1.0)));
            refuse("UnsupportedArgumentType", () -> p.call("extIO", List.of("wrong")));
            IOResult<?> effect = (IOResult<?>) p.call("extIO", List.of(1.25, 2.5));
            LeanChoice result = (LeanChoice) effect.value();
            check(!result.isLeft() && result.value().equals(List.of(1.25, 2.5)));
            check(effect.stdout().equals("floats\n") && effect.stderr().isEmpty());
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            check(Clojure.var("ansatz.lean.jvm", "call").invoke(p, "extSum", Clojure.read("{:left true}"))
                .equals(Clojure.read("{:right true}")));
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        }
        System.out.println("PASS ScalarInteropSmoke checks=" + checks + "; genuine v2 application JAR, no native toolchain");
    }
}
