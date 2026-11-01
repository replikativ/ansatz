import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Namespace;
import clojure.lang.Symbol;
import java.util.Collections;
public final class JarSmoke {
  static IFn op(String name) { return Clojure.var("ansatz.lean.jvm.ir", name); }
  public static void main(String[] args) throws Exception {
    Clojure.var("clojure.core", "require").invoke(Clojure.read("ansatz.lean.jvm.ir"));
    String resource = JarSmoke.class.getClassLoader().getResource("ansatz/lean/jvm/ir.clj").toString();
    if (!resource.startsWith("jar:")) throw new AssertionError("Adapter did not load from JAR");
    Object basis = op("linked-basis").invoke();
    Object rows = Clojure.read("[{\"kind\" \"decl\" \"name\" [\"str\" [\"anonymous\"] \"identity\"] \"ir\" {\"fdecl\" {\"f\" [\"str\" [\"anonymous\"] \"identity\"] \"xs\" [{\"x\" {\"idx\" 1} \"ty\" \"object\" \"borrow\" false}] \"type\" \"object\" \"body\" [\"ret\" {\"var\" {\"id\" {\"idx\" 1}}}]}}}]");
    Object ctx = op("prepare-host-program").invoke(basis, rows, Collections.emptyList());
    Object engine = op("machine").invoke(ctx);
    try {
      op("start!").invoke(ctx, engine, "identity", Collections.singletonList(37L));
      boolean done = false;
      for (int i=0; i<10 && !done; i++) done = (Boolean) op("advance!").invoke(ctx, engine, 10L);
      if (!done || !Long.valueOf(37L).equals(op("take-result!").invoke(ctx, engine))) throw new AssertionError("Explicit result");
      if (!Long.valueOf(42L).equals(op("call").invoke(ctx, engine, "identity", Collections.singletonList(42L)))) throw new AssertionError("Reused engine result");
    } finally { op("close!").invoke(ctx, engine); }
    for (String ns : new String[]{"prototype.machine", "prototype.unchanged-program-benchmark", "ansatz.lean"})
      if (Namespace.find(Symbol.intern(ns)) != null) throw new AssertionError("Unexpected backend " + ns);
    System.out.println("PASS jar-only canonical adapter, precompiled engine, repeated calls and close; no public Project API");
  }
}
