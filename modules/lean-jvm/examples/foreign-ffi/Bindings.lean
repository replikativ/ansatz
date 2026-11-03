namespace HostInterop

structure Message where
  count : Nat
  enabled : Bool
  deriving Inhabited

-- These declarations have no executable Lean reference implementation.
-- The explicit registry must provide every selected import before initialization.
@[extern "ansatz_jvm_length"] opaque length : String → Nat
@[extern "ansatz_jvm_message"] opaque makeMessage : Nat → Bool → Message
@[extern "ansatz_jvm_zero"] opaque zero : Nat
@[extern "ansatz_jvm_read_config"] opaque readConfig : String → IO String

-- Reference replacement remains useful when native Lean should run a fallback.
@[noinline] def referenceRead (key : String) : IO String :=
  pure ("reference:" ++ key)

end HostInterop
