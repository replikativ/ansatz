import Lean.Environment

namespace SourceReconstructionWitness

/-- Observe the actual frontend visibility flag without reading runtime offsets. -/
@[noinline] def isExporting (env : @& Lean.Environment) : Bool :=
  env.isExporting

end SourceReconstructionWitness
