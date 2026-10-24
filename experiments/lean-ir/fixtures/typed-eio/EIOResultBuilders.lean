namespace EIOResultBuilders
-- Real Lean constructor builders. No guessed IO.Result tag/field layout in host.
@[noinline] def success (value : String) : EIO String String := pure value
@[noinline] def failure (message : String) : EIO String String := throw message
end EIOResultBuilders
