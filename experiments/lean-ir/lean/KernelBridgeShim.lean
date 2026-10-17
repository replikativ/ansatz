import Lean

namespace KernelBridgeShim

-- These signatures match the existing exported Lean helpers. All arguments of
-- those helpers are owned; the compiler inserts retains when reusing a value.
@[extern "lean_environment_add"]
private opaque insertCheckedConstant
    (env : Lean.Kernel.Environment) (info : Lean.ConstantInfo) : Lean.Kernel.Environment

@[extern "lean_elab_environment_to_kernel_env"]
private opaque checkedKernelEnvironment (env : Lean.Environment) : Lean.Kernel.Environment

@[extern "lean_elab_environment_update_base_after_kernel_add"]
private opaque updateAfterKernelCheck
    (env : Lean.Environment) (kernel : Lean.Kernel.Environment)
    (decl : Lean.Declaration) : Lean.Environment

/-- Returns an owned reference to the precise checked kernel environment.
A host-side association must retain that owner while caching by guest identity. -/
@[noinline] def checkedKernelRoot (env : @& Lean.Environment) : Lean.Kernel.Environment :=
  env.toKernelEnv

/-- Owned identity witness for the exact checked persistent constant map.
Header-only environment updates may change the kernel root while sharing this
map. Hosts must also compare checkedQuotInit; equal sizes or names do not suffice. -/
@[noinline] def checkedConstantMapRoot (env : @& Lean.Environment) : Lean.ConstMap :=
  env.toKernelEnv.constants

/-- Establishes the only initial Java-environment association admitted by the
small bridge: both imported and local constant maps are demonstrably empty. -/
@[noinline] def checkedEnvironmentIsEmpty (env : @& Lean.Environment) : Bool :=
  let kernel := env.toKernelEnv
  let constants := kernel.constants
  !kernel.quotInit && constants.map₁.isEmpty && constants.map₂.isEmpty

/-- Enumerate the checked kernel maps, rather than provisional async frontend
constants. Imported association must check every returned value before anchoring
this exact kernel root. Array order is not kernel admission order. -/
@[noinline] def checkedConstants (env : @& Lean.Environment) : Array Lean.ConstantInfo :=
  (env.toKernelEnv.constants.toList.map Prod.snd).toArray

@[noinline] def checkedQuotInit (env : @& Lean.Environment) : Bool :=
  env.toKernelEnv.quotInit

/-- Post-check trust boundary ONLY. A host must first strictly admit this exact
declaration against the corresponding Java environment. This helper does not
check a declaration, reconstruct generated inductives, or publish executable code.

The environment is owned and declaration borrowed, matching `lean_elab_add_decl`.
The compiler retains borrowed values before passing them to owned helper APIs.
The caller's `Lean.Environment.addDeclCore` subsequently updates async constant maps.
No `addDeclWithoutChecking` fallback is installed or called. -/
@[noinline] unsafe def postCheckSafeDefinition
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .defnDecl value := decl
    | throw <| .other "KernelBridgeShim supports only a checked single definition"
  unless value.safety == .safe do
    throw <| .other "KernelBridgeShim supports only checked safe definitions"
  unless value.all == [value.name] do
    throw <| .other "KernelBridgeShim requires one-member definition metadata"
  let kernel := checkedKernelEnvironment env
  if kernel.find? value.name |>.isSome then
    throw <| .alreadyDeclared kernel value.name
  let updated := insertCheckedConstant kernel (.defnInfo value)
  return updateAfterKernelCheck env updated decl

/-- Post-check safe-axiom publication. The host must have strictly checked
this exact axiom against the corresponding Java environment before entering.
This function neither checks nor admits an unsafe axiom. -/
@[noinline] unsafe def postCheckSafeAxiom
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .axiomDecl value := decl
    | throw <| .other "KernelBridgeShim supports only a checked axiom"
  if value.isUnsafe then
    throw <| .other "KernelBridgeShim supports only checked safe axioms"
  let kernel := checkedKernelEnvironment env
  if kernel.find? value.name |>.isSome then
    throw <| .alreadyDeclared kernel value.name
  let updated := insertCheckedConstant kernel (.axiomInfo value)
  return updateAfterKernelCheck env updated decl

/-- Post-check publication for the exact compiler-marker bootstrap capability.
This does not permit general unsafe axioms. The host must strictly check this
same declaration first; all marker metadata is preserved unchanged. -/
@[noinline] unsafe def postCheckCompilerMarker
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .axiomDecl value := decl
    | throw <| .other "KernelBridgeShim compiler marker must be an axiom"
  unless value.isUnsafe && value.levelParams.isEmpty do
    throw <| .other "KernelBridgeShim compiler marker metadata mismatch"
  let .str .anonymous text := value.name
    | throw <| .other "KernelBridgeShim compiler marker name mismatch"
  unless text == "lcAny" || text == "lcErased" || text == "lcVoid" do
    throw <| .other "KernelBridgeShim compiler marker name mismatch"
  let .sort (.succ .zero) := value.type
    | throw <| .other "KernelBridgeShim compiler marker type mismatch"
  let kernel := checkedKernelEnvironment env
  if kernel.find? value.name |>.isSome then
    throw <| .alreadyDeclared kernel value.name
  let updated := insertCheckedConstant kernel (.axiomInfo value)
  return updateAfterKernelCheck env updated decl

/-- Post-check publication of the original DefinitionVal, including exact
safety, hints and nonsemantic mutual metadata. Host checking must use the native
safety-specific single-definition rule and explicit unsafe/partial policy first.
This helper does not check or axiomatize the body. -/
@[noinline] unsafe def postCheckDefinition
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .defnDecl value := decl | throw <| .other "Expected a strictly checked definition"
  let kernel := checkedKernelEnvironment env
  if kernel.find? value.name |>.isSome then
    throw <| .alreadyDeclared kernel value.name
  return updateAfterKernelCheck env (insertCheckedConstant kernel (.defnInfo value)) decl

/-- Post-check theorem publication: strictly admit this exact original
payload in the corresponding host Java environment before invoking. -/
@[noinline] unsafe def postCheckTheorem
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .thmDecl value := decl | throw <| .other "Expected a strictly checked theorem"
  let kernel := checkedKernelEnvironment env
  if kernel.find? value.name |>.isSome then
    throw <| .alreadyDeclared kernel value.name
  return updateAfterKernelCheck env (insertCheckedConstant kernel (.thmInfo value)) decl

/-- Post-check safe opaque publication; unsafe opaques remain unsupported until
native safety-mode parity has been established by the strict host checker. -/
@[noinline] unsafe def postCheckSafeOpaque
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .opaqueDecl value := decl | throw <| .other "Expected a strictly checked opaque declaration"
  if value.isUnsafe then throw <| .other "Unsafe opaque publication is unsupported"
  let kernel := checkedKernelEnvironment env
  if kernel.find? value.name |>.isSome then
    throw <| .alreadyDeclared kernel value.name
  return updateAfterKernelCheck env (insertCheckedConstant kernel (.opaqueInfo value)) decl

/-- Post-check mutual unsafe/partial publication. Every exact member must have
passed the host's strict group checker and explicit unsafe policy. Headers and
bodies are never checked by this publication helper. Preserve original metadata. -/
@[noinline] unsafe def postCheckMutualDefinitions
    (env : Lean.Environment) (decl : @& Lean.Declaration) :
    Except Lean.Kernel.Exception Lean.Environment := do
  let .mutualDefnDecl values := decl | throw <| .other "Expected a strictly checked mutual definition"
  let first :: _ := values | throw <| .other "Invalid empty mutual definition"
  if first.safety == .safe then throw <| .other "Mutual definitions must be unsafe or partial"
  let mut kernel := checkedKernelEnvironment env
  for value in values do
    unless value.safety == first.safety && value.levelParams == first.levelParams do
      throw <| .other "Mutual definition safety/universe parameters differ"
    if kernel.find? value.name |>.isSome then
      throw <| .alreadyDeclared kernel value.name
    kernel := insertCheckedConstant kernel (.defnInfo value)
  return updateAfterKernelCheck env kernel decl

/-- Atomic publication ONLY of a complete source-generated inductive family.
The host must have strictly generated/validated every member, decoded it using
real Lean constructors and reprojected the exact CI array against that result.
No native kernel call, incomplete-bundle fallback or synthesis happens here. -/
@[noinline] unsafe def postCheckGeneratedFamily
    (env : Lean.Environment) (decl : @& Lean.Declaration)
    (constants : Array Lean.ConstantInfo) : Except Lean.Kernel.Exception Lean.Environment := do
  let .inductDecl _ _ types unsafeFlag := decl | throw <| .other "Expected a checked source inductive declaration"
  if unsafeFlag then throw <| .other "Unsafe generated source inductive publication is unsupported"
  if constants.isEmpty || types.isEmpty then throw <| .other "Generated inductive family is empty"
  let all := types.map (·.name)
  let mut expected : Array (Lean.Name × Nat) := #[]
  for type in types do
    expected := expected.push (type.name, 5) |>.push (Lean.Name.str type.name "rec", 7)
    for ctor in type.ctors do expected := expected.push (ctor.name, 6)
  unless expected.size == constants.size do throw <| .other "Generated inductive family is incomplete"
  let mut kernel := checkedKernelEnvironment env
  for info in constants do
    let role ← match info with
      | .inductInfo value => do
        unless value.numNested == 0 && value.all == all && !value.isUnsafe do
          throw <| .other "Unsupported generated inductive metadata"
        pure 5
      | .ctorInfo _ => pure 6
      | .recInfo value => do
        unless value.all == all && !value.isUnsafe do throw <| .other "Generated recursor metadata mismatch"
        pure 7
      | _ => throw <| .other "Unexpected generated inductive family member"
    unless expected.contains (info.name, role) do throw <| .other "Unexpected generated inductive family name/role"
    if kernel.find? info.name |>.isSome then
      throw <| .alreadyDeclared kernel info.name
    kernel := insertCheckedConstant kernel info
  return updateAfterKernelCheck env kernel decl

/-- ABI fixture for the runtime error adapter; not a translation of all errors. -/
@[noinline] def otherError (message : String) : Except Lean.Kernel.Exception Lean.Environment :=
  .error (.other message)

end KernelBridgeShim

unsafe def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let original ← Lean.importModules #[{ module := `Init, importAll := true, isMeta := true }] {}
    (loadExts := true) (level := .private)
  let headerClone := original.setMainModule `KernelBridgeHeaderClone
  if ptrEq (KernelBridgeShim.checkedKernelRoot original)
      (KernelBridgeShim.checkedKernelRoot headerClone) then
    throw <| IO.userError "header update unexpectedly reused checked root"
  unless ptrEq (KernelBridgeShim.checkedConstantMapRoot original)
      (KernelBridgeShim.checkedConstantMapRoot headerClone) do
    throw <| IO.userError "header update changed checked constant map identity"
  unless KernelBridgeShim.checkedQuotInit original == KernelBridgeShim.checkedQuotInit headerClone do
    throw <| IO.userError "header update changed quotient initialization"
  IO.println "checked-header-clone-map-identity: passed"
  let empty ← Lean.mkEmptyEnvironment
  unless KernelBridgeShim.checkedEnvironmentIsEmpty empty do
    throw <| IO.userError "fresh checked environment is not empty"
  if KernelBridgeShim.checkedEnvironmentIsEmpty original then
    throw <| IO.userError "imported checked environment was classified as empty"
  unless (KernelBridgeShim.checkedKernelRoot empty).constants.map₁.isEmpty do
    throw <| IO.userError "checked root does not match the fresh environment"
  IO.println "checked-root-empty: passed; imported environment rejected"
  let name := `kernelBridgeOracleAnswer
  let value : Lean.DefinitionVal := {
    name, levelParams := [], type := Lean.mkConst ``Nat, value := Lean.mkNatLit 42,
    hints := .regular 2, safety := .safe, all := [name] }
  let declaration := Lean.Declaration.defnDecl value
  -- Required native checker success precedes every post-check helper invocation.
  let checked ← IO.ofExcept <| original.addDeclCore 1000000 1000 declaration none
    |>.mapError (fun _ => "native strict admission failed")
  let shim ← IO.ofExcept <| KernelBridgeShim.postCheckSafeDefinition original declaration
    |>.mapError (fun _ => "post-check reconstruction failed")
  unless (original.toKernelEnv.find? name).isNone do
    throw <| IO.userError "original environment changed"
  let some (.defnInfo checkedInfo) := checked.toKernelEnv.find? name
    | throw <| IO.userError "native checked result missing"
  let some (.defnInfo shimInfo) := shim.toKernelEnv.find? name
    | throw <| IO.userError "shim result missing"
  unless checkedInfo == shimInfo do
    throw <| IO.userError "post-check constant differs from native admission"
  let axiomName := `kernelBridgeOracleType
  let axiomValue : Lean.AxiomVal := {
    name := axiomName, levelParams := [], type := Lean.mkSort (.succ .zero), isUnsafe := false }
  let axiomDeclaration := Lean.Declaration.axiomDecl axiomValue
  let checkedAxiom ← IO.ofExcept <| original.addDeclCore 1000000 1000 axiomDeclaration none
    |>.mapError (fun _ => "native strict axiom admission failed")
  let shimAxiom ← IO.ofExcept <| KernelBridgeShim.postCheckSafeAxiom original axiomDeclaration
    |>.mapError (fun _ => "post-check axiom reconstruction failed")
  unless (original.toKernelEnv.find? axiomName).isNone do
    throw <| IO.userError "original environment changed during axiom admission"
  let some (.axiomInfo checkedAxiomInfo) := checkedAxiom.toKernelEnv.find? axiomName
    | throw <| IO.userError "native checked axiom missing"
  let some (.axiomInfo shimAxiomInfo) := shimAxiom.toKernelEnv.find? axiomName
    | throw <| IO.userError "post-check axiom missing"
  unless checkedAxiomInfo == shimAxiomInfo do
    throw <| IO.userError "post-check axiom differs from native admission"
  match KernelBridgeShim.postCheckSafeAxiom shimAxiom axiomDeclaration with
  | .error (.alreadyDeclared _ n) =>
    unless n == axiomName do throw <| IO.userError "wrong duplicate axiom name"
  | _ => throw <| IO.userError "duplicate axiom was not rejected"
  match KernelBridgeShim.postCheckSafeAxiom original (.axiomDecl { axiomValue with isUnsafe := true }) with
  | .error (.other _) => pure ()
  | _ => throw <| IO.userError "unsafe axiom was not rejected"
  IO.println "native-check-before-axiom-shim: passed; duplicate and unsafe rejected"
  for markerName in [`lcAny, `lcErased, `lcVoid] do
    let marker : Lean.AxiomVal := {
      name := markerName, levelParams := [], type := Lean.mkSort (.succ .zero), isUnsafe := true }
    let markerDeclaration := Lean.Declaration.axiomDecl marker
    let nativeMarker ← IO.ofExcept <| empty.addDeclCore 1000000 1000 markerDeclaration none
      |>.mapError (fun _ => "native strict compiler marker admission failed")
    let publishedMarker ← IO.ofExcept <| KernelBridgeShim.postCheckCompilerMarker empty markerDeclaration
      |>.mapError (fun _ => "post-check compiler marker reconstruction failed")
    let some (.axiomInfo nativeInfo) := nativeMarker.toKernelEnv.find? markerName
      | throw <| IO.userError "native compiler marker missing"
    let some (.axiomInfo publishedInfo) := publishedMarker.toKernelEnv.find? markerName
      | throw <| IO.userError "published compiler marker missing"
    unless nativeInfo == publishedInfo do
      throw <| IO.userError "compiler marker differs from native checking"
    match KernelBridgeShim.postCheckCompilerMarker publishedMarker markerDeclaration with
    | .error (.alreadyDeclared _ name) =>
      unless name == markerName do throw <| IO.userError "wrong duplicate marker name"
    | _ => throw <| IO.userError "duplicate compiler marker was not rejected"
    let invalidMarkers : List Lean.AxiomVal := [
      { marker with name := `notACompilerMarker },
      { marker with name := `Nested.lcAny },
      { marker with type := Lean.mkSort .zero },
      { marker with type := Lean.mkSort (.max (.succ .zero) .zero) },
      { marker with levelParams := [`u] },
      { marker with isUnsafe := false }]
    for invalid in invalidMarkers do
      match KernelBridgeShim.postCheckCompilerMarker empty (.axiomDecl invalid) with
      | .error (.other _) => pure ()
      | _ => throw <| IO.userError "invalid compiler marker was not rejected"
  IO.println "compiler-marker-only: native checked; exact three preserved; nearby cases rejected"
  match KernelBridgeShim.otherError "expected adapter failure" with
  | .error (.other message) => IO.println s!"error-other: {message}"
  | _ => throw <| IO.userError "wrong error representation"
  IO.println "native-check-before-shim: passed"
  IO.println "new checked constant: Nat := 42; original unchanged"
  IO.println "frontend async publication and executable installation remain caller obligations"
