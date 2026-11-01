namespace ProjectAppEIO
-- Native export is an ABI oracle; the hosted binding replaces this fallback.
@[extern "ansatz_app_eio_text"]
opaque hostText (input : String) : EIO String String := pure input

@[noinline] def run (input : String) : IO String :=
  EIO.toIO IO.Error.userError (hostText input)

-- Both outcomes are handled inside Lean. No literal/closed initializer is needed.
@[noinline] def handled (input : String) : IO String := do
  match ← EIO.toIO' (hostText input) with
  | .ok value => pure value
  | .error message => pure message

-- Sequencing/effect test: an unused first result must not eliminate the call.
@[noinline] def twice (input : String) : IO String := do
  let _ ← run input
  run input
end ProjectAppEIO
