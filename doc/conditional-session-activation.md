# Conditional session activation

`session/activate-if-unchanged! expected prepared` validates both complete
ProofContexts, checks captured identities under `state/session-lock`, and attempts
one Env CAS. It does not retry. Store handles remain borrowed.

The result is one of:

- `{:status :activated :session prepared}` after all actual prepared leaves pass
  identity checks.
- `{:status :rejected :stage ... :changed [...]}` for invalid input, a failed
  capture, stale captured state, a false CAS, or nested conditional activation.
  Validation/capture failures retain `:cause`; a false CAS includes an observation.
- `{:status :failed :stage ... :cause original :restoration report}` after an
  installation exception or detected callback conflict. The original exception
  remains the cause when one exists.

Participating leaves are the six session slots, synthesis map, instance cache,
simp-index cache, and simp function-information cache's separate Env and entries.
Snapshot cache wrapper and Atom objects are deliberately not compared because
capture creates fresh wrappers. Unknown extension fields on a ProofContext do
not become additional installed globals.

Every shared installation step is followed by a check against its expected
intermediate state, including immediately after a successful Env CAS. Silent
watch mutations therefore cannot produce a false successful outcome. Each cache
restore hook is one step; a hook may contain multiple underlying Atom writes.
The final check verifies the complete prepared state again.

A foreign Env or unexpected leaf causes publication to stop with a conflicted
report containing the observed session. It does not blindly restore over that
session. On exceptions, best-effort restoration writes only while every observed
leaf belongs to the old/prepared transition. Restoration checks actual leaves
even when a validator/watch/hook throws; distinct restoration exceptions are
reported and suppressed on the original cause without self-suppression.
The report's `:restored`, `:failed` or `:conflicted` status describes actual
observed restoration, with `:changed` keys and `:errors` when available. A watch
exception may accompany fully restored state because watches run after mutation.

Nested conditional activation is rejected. Legacy `activate!` or `with-session`
called from a callback during conditional installation/restoration throws before
performing its nested installation. Outside the new conditional operation their
existing behavior and restoration policy remain unchanged.

This is the existing cooperative lock contract, not isolation from unlocked
writers/readers, multi-atom atomic visibility, or rollback of watch side effects.
An unlocked writer can act after any observation. A foreign value equal by
identity to an owned transition value cannot be distinguished from that owned
value. The API does not claim to undo IO, namespace Vars or external resources.
