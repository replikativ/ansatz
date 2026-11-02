import ansatz.lean.jvm.*;
import clojure.java.api.Clojure;
import clojure.lang.IPersistentMap;
import clojure.lang.Keyword;

/** Unchanged installed-library regression via an authenticated, JVM-only artifact. */
public final class PersistentMapSmoke {
    private static final String MANIFEST = "e3c6f3abd02de8db069dee192a9b970280247d031b6214146d4121f381cd15da";
    private static int checks;
    private static void check(boolean ok) {
        checks++;
        if (!ok) throw new AssertionError("check " + checks);
    }
    public static void main(String[] args) throws Exception {
        LeanFunction retained;
        try (Lean runtime = Lean.open();
             LeanProject project = runtime.loadArtifact(PersistentMapSmoke.class.getClassLoader(),
                                                        "lean/persistent-map.zip", MANIFEST)) {
            retained = project.function("main");
            check(retained.arity() == 0);
            for (int i = 0; i < 3; i++) {
                IOResult<?> result = (IOResult<?>) retained.invoke();
                check(result.value() == LeanUnit.INSTANCE);
                check(result.stdout().equals("OK\n"));
                check(result.stderr().isEmpty());
            }
            Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm"));
            IPersistentMap result = (IPersistentMap) Clojure.var("ansatz.lean.jvm", "call").invoke(project, "main");
            check(result.valAt(Keyword.intern("value")) == null);
            check(result.valAt(Keyword.intern("stdout")).equals("OK\n"));
            check(result.valAt(Keyword.intern("stderr")).equals(""));
            check(Clojure.var("clojure.core", "find-ns").invoke(Clojure.read("ansatz.lean.jvm.compiler.transport")) == null);
        }
        try {
            retained.invoke();
            throw new AssertionError("closed handle accepted");
        } catch (IllegalStateException expected) {
            check(expected.getMessage().contains("closed"));
        }
        System.out.println("PERSISTENT_MAP_SMOKE checks=" + checks + "; installed-library artifact, JVM-only");
    }
}
