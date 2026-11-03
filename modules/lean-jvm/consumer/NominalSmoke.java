import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IFn;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

/** Independent application-JAR consumer of native-derived nominal datatypes. */
public final class NominalSmoke {
    private static final String MANIFEST = "06f1ccafd17b4cdc8915b2e41d49e8e9741b8765fa2b281b60bcce636c5daf25";
    private static final String PREFIX = "DatatypeExample.";
    private static void require(boolean ok, String message) {
        if (!ok) throw new AssertionError(message);
    }
    private static BigInteger n(long value) { return BigInteger.valueOf(value); }
    private static LeanProject load(Lean runtime) throws Exception {
        return runtime.loadArtifact(NominalSmoke.class.getClassLoader(), "lean/datatypes.zip", MANIFEST);
    }
    private static LeanType.Constructor constructor(LeanType type, String leaf) {
        return type.constructors().stream().filter(c -> c.name().stringPart().equals(leaf))
                .findFirst().orElseThrow(() -> new AssertionError("Missing native constructor " + leaf));
    }
    private static LeanData literal(LeanType tree, long value) {
        return constructor(tree, "literal").create(List.of(n(value)));
    }
    private static void refused(String code, Runnable call) {
        try { call.run(); throw new AssertionError("Expected " + code); }
        catch (LeanException failure) { require(code.equals(failure.code()), "Expected " + code + ", got " + failure.code()); }
    }
    private static void healthy(LeanProject project, LeanData tree) {
        require(project.call(PREFIX + "eval", tree).equals(n(33)), "Input refusal poisoned Project");
    }
    public static void main(String[] args) throws Exception {
        LeanData retained;
        LeanType retainedType;
        Map<String, Object> retainedDescriptor;
        try (Lean runtime = Lean.open()) {
            try (LeanProject project = load(runtime)) {
                LeanFunction sample = project.function(PREFIX + "sample");
                LeanFunction eval = project.function(PREFIX + "eval");
                LeanFunction summarize = project.function(PREFIX + "summarize");
                require(sample.hasTypeMetadata() && eval.hasTypeMetadata(), "Missing native-derived type metadata");
                LeanType treeType = sample.resultType();
                require(treeType.kind() == LeanType.Kind.NOMINAL && treeType.equals(eval.argumentTypes().get(0)),
                        "Imported defining-module type identity differs");
                require(!treeType.equals(summarize.resultType()), "Distinct nominal types were conflated");
                require(((List<?>) eval.descriptor().get("arguments")).get(0).equals(treeType)
                                && eval.descriptor().get("result").equals(eval.resultType()),
                        "Closed descriptor omitted detached type identity");
                retainedDescriptor = sample.descriptor();
                retainedType = treeType;
                retained = (LeanData) sample.invoke(n(11));
                healthy(project, retained);
                LeanData simplified = (LeanData) project.call(PREFIX + "simplify", retained);
                require(simplified.constructor().name().stringPart().equals("literal") && simplified.field(0).equals(n(33)),
                        "Simplification did not fold the expression");
                LeanData stats = (LeanData) summarize.invoke(retained);
                require(stats.field(0).equals("expression") && stats.field(1).equals(n(33))
                                && stats.field(2).equals(n(9)) && stats.field(3).equals(n(4))
                                && stats.field(4).equals(true) && stats.field(5).equals(List.of(n(11), n(9), n(7), n(0), n(3))),
                        "Native record fields differ");
                require(project.call(PREFIX + "readStats", stats).equals(List.of(n(33), n(9), n(4), n(1), n(5), n(30), n(10))),
                        "Native record reader differs");

                LeanType.Constructor binary = constructor(treeType, "binary");
                LeanType opType = binary.fields().get(0).type();
                LeanData add = constructor(opType, "add").create(List.of());
                LeanData hostSum = binary.create(List.of(add, literal(treeType, 4), literal(treeType, 5)));
                require(eval.invoke(hostSum).equals(n(9)), "Host expression did not reach independent evaluator");
                LeanData hostChoice = constructor(treeType, "choose").create(List.of(false, literal(treeType, 4), literal(treeType, 5)));
                require(eval.invoke(hostChoice).equals(n(5)), "Host conditional chose another branch");
                LeanType statsType = summarize.resultType();
                LeanData hostStats = constructor(statsType, "mk").create(List.of("host", n(17), n(3), n(2), false, List.of(n(8), n(9))));
                require(project.call(PREFIX + "readStats", hostStats).equals(List.of(n(17), n(3), n(2), n(0), n(2), n(17), n(4))),
                        "Host record did not reach independent reader");

                IOResult<?> echoed = (IOResult<?>) project.call(PREFIX + "ioEcho", retained);
                require(echoed.value().equals(retained) && echoed.stdout().equals("value=33\n") && echoed.stderr().isEmpty(),
                        "IO success lost custom payload or captured output");
                refused("InvalidArgument", () -> eval.invoke("not an expression"));
                healthy(project, retained);
                LeanBytes bytes = LeanBytes.copyOf(new byte[600_000]);
                LeanBytes independent = LeanBytes.copyOf(new byte[600_000]);
                refused("ResourceLimit", () -> project.call(PREFIX + "byteTotal", bytes, independent));
                healthy(project, retained);
                require(project.call(PREFIX + "byteTotal", bytes, bytes).equals(n(1_200_000)),
                        "Certified shared byte payload was charged twice");

                Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
                IFn clojureCheck = (IFn) Clojure.var("clojure.core", "eval").invoke(Clojure.read(
                        "(fn [p] (let [tree (ansatz.lean.jvm/call p \"DatatypeExample.sample\" 11) " +
                        "{type :lean/type ctor :lean/constructor fields :lean/fields} tree " +
                        "plain (ansatz.lean.jvm/materialize tree)] " +
                        "(and (map? tree) (= 3 (count tree)) " +
                        "(instance? ansatz.lean.jvm.LeanTypeId type) (= \"binary\" (.stringPart ctor)) " +
                        "(= 3 (count fields)) (= tree plain) " +
                        "(= 33 (ansatz.lean.jvm/call p \"DatatypeExample.eval\" tree)) " +
                        "(= 33 (ansatz.lean.jvm/call p \"DatatypeExample.eval\" plain)))))"));
                require(Boolean.TRUE.equals(clojureCheck.invoke(project)), "Clojure view/destructuring/materialization differs");
                require(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null,
                        "Artifact consumer loaded native compiler namespace");
            }

            // Retained values and construction descriptors contain no producing Project.
            require(retainedType.nominalId().orElseThrow().equals(retained.type().nominalId().orElseThrow())
                            && retainedDescriptor.get("result").equals(retainedType), "Detached descriptors changed after close");
            LeanData afterClose = literal(retainedType, 42);
            try (LeanProject first = load(runtime); LeanProject second = load(runtime)) {
                healthy(first, retained);
                require(first.call(PREFIX + "eval", afterClose).equals(n(42)), "Detached descriptor cannot construct after close");
                require(first.function(PREFIX + "eval").argumentTypes().get(0).equals(retainedType),
                        "Fresh Project changed defining-module identity");
                var pool = Executors.newFixedThreadPool(2);
                try {
                    var left = pool.submit(() -> first.call(PREFIX + "eval", retained));
                    var right = pool.submit(() -> second.call(PREFIX + "eval", retained));
                    require(left.get(10, TimeUnit.SECONDS).equals(n(33)) && right.get(10, TimeUnit.SECONDS).equals(n(33)),
                            "Concurrent Projects could not reuse detached storage");
                } finally {
                    pool.shutdownNow();
                    require(pool.awaitTermination(10, TimeUnit.SECONDS), "Concurrent consumer workers did not stop");
                }
            }
            try (LeanProject errors = load(runtime)) {
                LeanData zero = literal(errors.function(PREFIX + "ioCheckedEcho").argumentTypes().get(0), 0);
                try {
                    errors.call(PREFIX + "ioCheckedEcho", zero);
                    throw new AssertionError("Zero-valued IO payload was accepted");
                } catch (LeanException error) {
                    require(error.code().equals("GuestIOError") && error.details().equals(Map.of("kind", "userError", "message", "zero-valued expression")),
                            "IO error lost bounded native userError details");
                }
            }
        }
        System.out.println("PASS native-free nominal Java/Clojure constructors, descriptors, IO payloads, refusal recovery, shared bytes, close survival and concurrent Project reuse; application JAR");
    }
}
