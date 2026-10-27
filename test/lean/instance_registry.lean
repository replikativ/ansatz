-- Lean Meta/Instances.lean: only declarations registered with addInstance are candidates.
class RegistryFlag where
  value : Nat

@[instance_reducible] def instUnregisteredFlag : RegistryFlag := ⟨1⟩

example : True := by
  fail_if_success have : RegistryFlag := inferInstance
  trivial

instance registeredFlag : RegistryFlag := ⟨2⟩
example : RegistryFlag.value = 2 := rfl

-- Classical.propDecidable is scoped, so a declaration's name cannot make it a candidate.
example (_p : Prop) : True := by
  fail_if_success have : Decidable _p := inferInstance
  trivial
