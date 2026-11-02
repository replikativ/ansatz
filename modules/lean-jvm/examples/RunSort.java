import ansatz.lean.jvm.IOResult;
import ansatz.lean.jvm.Lean;
import ansatz.lean.jvm.LeanProject;
import ansatz.lean.jvm.NativeCompilerOptions;
import ansatz.lean.jvm.ProjectOptions;
import java.math.BigInteger;
import java.nio.file.Path;
import java.util.List;

/** Source-loading example; all paths are explicit, and compilation is trusted. */
public final class RunSort {
    public static void main(String[] args) {
        if (args.length != 4) throw new IllegalArgumentException("source-root lean-sysroot producer-bundle compiler-cache");
        NativeCompilerOptions compiler = new NativeCompilerOptions(Path.of(args[1]), Path.of(args[2]), Path.of(args[3]));
        ProjectOptions options = ProjectOptions.builder(compiler).rootModule("Tutorial")
            .function("Tutorial.sortNats").function("Tutorial.sortStrings")
            .function("Tutorial.sortAndOriginal").build();
        try (Lean runtime = Lean.open(); LeanProject project = runtime.loadProject(Path.of(args[0]), options)) {
            IOResult result = (IOResult) project.call("Tutorial.sortAndOriginal",
                List.of(BigInteger.valueOf(3), BigInteger.valueOf(2), BigInteger.ONE));
            System.out.println(result.value());
            System.err.print(result.stderr());
        }
    }
}
