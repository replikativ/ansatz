-- Native baseline only; the hosted loader must execute these helpers as guest IR.
-- Reproduce with the pinned toolchain:
-- mkdir -p target/file-shim-tests
-- lean +leanprover/lean4:v4.33.1 --root=lean -o target/file-shim-tests/RuntimeCompileShim.olean lean/RuntimeCompileShim.lean
-- LEAN_NUM_THREADS=1 LEAN_PATH=target/file-shim-tests lean +leanprover/lean4:v4.33.1 lean/RuntimeCompileShimFileTests.lean
import RuntimeCompileShim

open Lean

namespace RuntimeCompileShimFileTests

private def field (j : Json) (name : String) : IO Json :=
  IO.ofExcept (j.getObjVal? name)
private def bool (j : Json) (name : String) : IO Bool :=
  IO.ofExcept (j.getObjValAs? Bool name)
private def text (j : Json) (name : String) : IO String :=
  IO.ofExcept (j.getObjValAs? String name)
private def parsed (s : String) : IO Json := IO.ofExcept (Json.parse s)
private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message
private def check (label : String) (success : Bool) (stage : String) (result : String) : IO Json := do
  let j ← parsed result
  ensure ((← bool j "success") == success) s!"{label}: unexpected result: {result}"
  ensure ((← text j "stage") == stage) s!"{label}: unexpected stage: {result}"
  if success then
    ensure (!(← text j "bundle").isEmpty) s!"{label}: no bundle"
  else
    ensure (!(← IO.ofExcept ((← field j "diagnostics").getArr?)).isEmpty) s!"{label}: missing diagnostics"
    ensure ((← field j "bundle") == Json.null) s!"{label}: failed compilation published bundle"
  IO.println s!"PASS {label}"
  return j

unsafe def run : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let opts : Options := {}
  let imports : Array Import := #[{module := `Init}, {module := `Init, isMeta := true}]
  let env ← importModules imports opts 0 (loadExts := true)
  let header ← parsed (← RuntimeCompileShim.inspectFileHeader "def answer : Nat := 42\n" "Default.lean")
  ensure (!(← bool header "hasErrors")) "default header failed"
  ensure ((← IO.ofExcept ((← field header "requestedImports").getArr?)).size == 2) "implicit Init imports lost"
  let prelude ← parsed (← RuntimeCompileShim.inspectFileHeader "prelude\n" "Prelude.lean")
  ensure ((← IO.ofExcept ((← field prelude "requestedImports").getArr?)).isEmpty) "prelude gained imports"
  let flagged ← parsed (← RuntimeCompileShim.inspectFileHeader "module\npublic meta import Init\nmeta import all Init\n" "Flags.lean")
  ensure (!(← bool flagged "hasErrors") && (← bool flagged "moduleSystem")) "module header flags parse failed"
  let flags ← IO.ofExcept ((← field flagged "requestedImports").getArr?)
  ensure (flags.size == 4) "module implicit Init imports lost"
  ensure (!(← bool flags[2]! "importAll") && (← bool flags[2]! "isExported") && (← bool flags[2]! "isMeta") &&
          (← bool flags[3]! "importAll") && !(← bool flags[3]! "isExported") && (← bool flags[3]! "isMeta")) "exact import flags lost"
  IO.println "PASS header-default-and-prelude"
  let (compiled, result) ← RuntimeCompileShim.compileImportedFileState env
    "def answer : Nat := 42\n" "Default.lean" `Default #[`answer] opts
  let _ ← check "default-Init-answer" true "complete" result
  ensure (compiled.contains `answer && compiled.mainModule == `Default) "final environment was dropped"
  ensure (!(env.contains `answer)) "input environment mutated"
  ensure ((← IO.ofExcept (compiled.evalConst Nat opts `answer)) == 42) "compiled answer execution differs"
  let custom := "namespace Example\nmacro \"fortyTwo\" : term => `(42)\ndef answer : Nat := fortyTwo\nend Example\n"
  let (customEnv, result) ← RuntimeCompileShim.compileImportedFileState env custom
    "Macro.lean" `Macro #[`Example.answer] opts
  let _ ← check "namespace-and-custom-macro" true "complete" result
  ensure ((← IO.ofExcept (customEnv.evalConst Nat opts `Example.answer)) == 42) "macro result differs"
  let (continued, result) ← RuntimeCompileShim.compileImportedFileState compiled
    "def following : Nat := answer + 1\n" "Following.lean" `Following #[`following] opts
  let _ ← check "retained-environment-continuation" true "complete" result
  ensure ((← IO.ofExcept (continued.evalConst Nat opts `following)) == 43) "retained environment unusable"
  let (badHeaderEnv, result) ← RuntimeCompileShim.compileImportedFileState env
    "import\n" "BadHeader.lean" `BadHeader #[`answer] opts
  let _ ← check "bad-header" false "header" result
  ensure (ptrEq env badHeaderEnv) "header failure replaced original environment"
  let (_, result) ← RuntimeCompileShim.compileImportedFileState env
    "prelude\ndef answer : Nat := 42\n" "Mismatch.lean" `Mismatch #[`answer] opts
  let _ ← check "mismatched-imports" false "imports" result
  let (_, result) ← RuntimeCompileShim.compileImportedFileState env
    "module\nmeta import all Init\ndef answer : Nat := 42\n" "Flags.lean" `Flags #[`answer] opts
  let _ ← check "mismatched-import-flags" false "imports" result
  let (_, result) ← RuntimeCompileShim.compileImportedFileState env
    "module\ndef answer : Nat := 42\n" "Module.lean" `Module #[`answer] opts
  let _ ← check "mismatched-module-mode" false "imports" result
  enableInitializersExecution
  let reversed ← importModules imports.reverse opts 0 (loadExts := true)
  let (_, result) ← RuntimeCompileShim.compileImportedFileState reversed
    "def answer : Nat := 42\n" "Order.lean" `Order #[`answer] opts
  let _ ← check "same-module-names-wrong-import-order" false "imports" result
  let empty ← mkEmptyEnvironment
  let (preludeEnv, result) ← RuntimeCompileShim.compileImportedFileState empty
    "prelude\naxiom HostedSort : Sort 1\n" "Prelude.lean" `Prelude #[] opts
  let _ ← check "prelude-no-imports" true "complete" result
  ensure (preludeEnv.contains `HostedSort) "prelude declaration missing"
  let (_, result) ← RuntimeCompileShim.compileImportedFileState env
    "set_option autoImplicit false\ndef answer : Nat := unknownTerm\n" "BadCommand.lean" `BadCommand #[`answer] opts
  let _ ← check "command-diagnostics" false "commands" result
  let (partialEnv, result) ← RuntimeCompileShim.compileImportedFileState env
    "def beforeError : Nat := 7\ndef broken : Nat := unknownTerm\n" "Partial.lean" `Partial #[`beforeError] opts
  let j ← check "post-error-environment-retained" false "commands" result
  ensure (partialEnv.contains `beforeError && partialEnv.mainModule == `Partial) "post-error state was dropped"
  ensure ((← text j "environmentState") == "after-commands") "post-error state undocumented"
  let (_, result) ← RuntimeCompileShim.compileImportedFileState env
    "def answer : Nat := 42\n" "Missing.lean" `Missing #[`missing] opts
  let _ ← check "missing-executable-root" false "exports" result
  let strict := opts.setBool `autoImplicit false
  let (_, result) ← RuntimeCompileShim.compileImportedFileState env
    "def bad (x : UnknownType) := x\n" "Options.lean" `Options #[`bad] strict
  let _ ← check "supplied-options-applied" false "commands" result
  IO.println "ALL FILE SHIM CASES PASS"

end RuntimeCompileShimFileTests

#eval RuntimeCompileShimFileTests.run
