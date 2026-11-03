package ansatz.lean.jvm;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/** Requested native checked entries and explicit source compilation policy. */
public final class ProjectOptions {
    /** Resource bound on selected host-callable functions; independent of function arity. */
    public static final int MAX_SELECTED_ENTRIES = 1024;
    public static final int MAX_INSTALLED_IMPORTS = 128;
    public static final class Entry {
        private final String name;
        private final String signature;
        private Entry(String name, String signature) {
            this.name = Objects.requireNonNull(name, "name");
            this.signature = signature;
        }
        public String name() { return name; }
        public String signature() { return signature; }
    }

    public static final class Builder {
        private final NativeCompilerOptions compiler;
        private String module = "Main";
        private final List<Entry> entries = new ArrayList<>();
        private final List<String> installedImports = new ArrayList<>();
        private String sourceRoot = ".";
        private boolean builtLakeWorkspace;
        private Builder(NativeCompilerOptions compiler) {
            this.compiler = Objects.requireNonNull(compiler, "compiler");
        }
        public Builder sourceRoot(String relativeDirectory) {
            sourceRoot = Objects.requireNonNull(relativeDirectory, "relativeDirectory");
            return this;
        }
        public Builder rootModule(String module) {
            this.module = Objects.requireNonNull(module, "module");
            return this;
        }
        /** Permit one exact installed module; list its entire non-Init import closure. */
        public Builder installedImport(String module) {
            Objects.requireNonNull(module, "module");
            if (installedImports.size() >= MAX_INSTALLED_IMPORTS || installedImports.contains(module))
                throw new IllegalArgumentException("Installed imports must be distinct and bounded");
            installedImports.add(module);
            return this;
        }
        /** Consume an already resolved and built Lake workspace; never issue a build/update. */
        public Builder builtLakeWorkspace() { builtLakeWorkspace = true; return this; }
        public Builder main(String name) { entries.add(new Entry(name, "io-unit")); return this; }
        /** Ask a v2 native producer to discover and check the closed signature. */
        public Builder function(String name) { entries.add(new Entry(name, "auto")); return this; }
        public Builder natFunction(String name) { entries.add(new Entry(name, "nat-to-nat")); return this; }
        public Builder stringFunction(String name) { entries.add(new Entry(name, "string-to-string")); return this; }
        public ProjectOptions build() {
            if (entries.isEmpty() || entries.size() > MAX_SELECTED_ENTRIES)
                throw new IllegalArgumentException("Request one to " + MAX_SELECTED_ENTRIES + " checked entries");
            if (builtLakeWorkspace && (!sourceRoot.equals(".") || !installedImports.isEmpty()))
                throw new IllegalArgumentException("Lake mode discovers roots/imports; sourceRoot and installedImport overrides are unsupported");
            return new ProjectOptions(compiler, sourceRoot, module, entries, installedImports, builtLakeWorkspace);
        }
    }

    private final NativeCompilerOptions compiler;
    private final String sourceRoot;
    private final boolean builtLakeWorkspace;
    private final String module;
    private final List<Entry> entries;
    private final List<String> installedImports;

    private ProjectOptions(NativeCompilerOptions compiler, String sourceRoot, String module, List<Entry> entries,
                           List<String> installedImports, boolean builtLakeWorkspace) {
        this.compiler = compiler;
        this.builtLakeWorkspace = builtLakeWorkspace;
        this.sourceRoot = sourceRoot;
        this.module = module;
        this.entries = List.copyOf(entries);
        this.installedImports = List.copyOf(installedImports);
    }

    public static Builder builder(NativeCompilerOptions compiler) { return new Builder(compiler); }
    public NativeCompilerOptions compiler() { return compiler; }
    public String sourceRoot() { return sourceRoot; }
    public boolean builtLakeWorkspace() { return builtLakeWorkspace; }
    public String rootModule() { return module; }
    public List<Entry> entries() { return entries; }
    public List<String> installedImports() { return installedImports; }
}
