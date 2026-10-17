import RuntimeCompileShim

open Lean

-- Generate actual compiler IR without ever executing an external host symbol.
-- Both opaque declarations have safe checked fallback values, with no sorry.
-- Compile RuntimeCompileShim.olean into target/file-shim-tests first (see the
-- file helper tests), then run with the pinned toolchain and matching
-- LEAN_SYSROOT, LEAN_PATH=target/file-shim-tests. Stdout is the JSONL fixture.
unsafe def generateHostInteropFixture : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Init}, {module := `Init, isMeta := true}] {} 0 (loadExts := true)
  let source := "namespace HostInteropProbe\n@[extern \"ansatz_host_double\"] opaque hostDouble (x : UInt32) : UInt32 := x\ndef roundTrip (x : UInt32) : UInt32 := hostDouble x\n@[extern \"ansatz_host_string\"] opaque hostString (s : String) : IO String := pure s\ndef roundTripString (s : String) : IO String := hostString s\nend HostInteropProbe\n"
  let (env, result) ← RuntimeCompileShim.compileImportedFileState env source
    "HostInteropProbe.lean" `HostInteropProbe
    #[`HostInteropProbe.roundTrip, `HostInteropProbe.roundTripString] {}
  let envelope ← IO.ofExcept (Json.parse result)
  unless (← IO.ofExcept (envelope.getObjValAs? Bool "success")) do
    throw <| IO.userError result
  for name in #[`HostInteropProbe.hostDouble, `HostInteropProbe.hostString] do
    let some (.opaqueInfo value) := env.find? name
      | throw <| IO.userError "expected a checked opaque host declaration"
    if value.isUnsafe then throw <| IO.userError "unsafe host declaration"
  IO.print (← IO.ofExcept (envelope.getObjValAs? String "bundle"))

#eval generateHostInteropFixture
