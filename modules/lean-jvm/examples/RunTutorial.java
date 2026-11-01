import ansatz.lean.jvm.Lean;
import ansatz.lean.jvm.LeanProject;
import ansatz.lean.jvm.NativeCompilerOptions;
import ansatz.lean.jvm.ProjectOptions;
import java.nio.file.Path;

/** Run unchanged FP Lean first-lake sources; source compilation is explicit. */
public final class RunTutorial {
    public static void main(String[] args) {
        if (args.length != 4) {
            throw new IllegalArgumentException("Expected: project-directory lean-sysroot producer-bundle cache-directory");
        }
        var compiler = new NativeCompilerOptions(Path.of(args[1]), Path.of(args[2]), Path.of(args[3]));
        var options = ProjectOptions.builder(compiler).rootModule("Main").main("main").build();
        try (Lean lean = Lean.open(); LeanProject project = lean.loadProject(Path.of(args[0]), options)) {
            for (int i = 0; i < 2; i++) {
                var result = project.runMain();
                if (!result.stdout().equals("Hello, world!\n") || !result.stderr().isEmpty()) {
                    throw new AssertionError("Unexpected tutorial output");
                }
                System.out.print(result.stdout());
            }
        }
    }
}
