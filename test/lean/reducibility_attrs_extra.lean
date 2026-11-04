import reducibility_attrs

-- Lean 4.33.1 ReducibilityAttrs.lean:setReducibilityStatusCore sends changes
-- to imported declarations through reducibilityExtraExt, rather than the core.
set_option allowUnsafeReducibility true
attribute [irreducible] ReducibilityFixture.changedInImport

open Lean in
run_meta do
  unless (← getReducibilityStatus `ReducibilityFixture.changedInImport) == .irreducible do
    throwError "imported extra reducibility status was lost"
