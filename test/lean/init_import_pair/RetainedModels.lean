import RetainedA
import RetainedB
-- Lean v4.33.1 Environment.lean importModulesCore deduplicates the shared Init.
example : True ∧ True := And.intro retainedModelA retainedModelB
