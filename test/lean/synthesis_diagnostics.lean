import Init

-- Expected diagnostics from Lean v4.33.1 (819816b2e0).

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
inductive MissingOrder (A : Type) where
 | mk (x : A) (h : x ≤ x)

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
def missingOrderDef (A : Type) (x : A) : Prop := x ≤ x

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Tactic `assumption` failed

A : Type
x : A
⊢ sorry
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : x ≤ x := by assumption

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
structure MissingOrderStruct (A : Type) where
 x : A
 h : x ≤ x

/--
error: don't know how to synthesize placeholder
context:
⊢ Nat
-/
#guard_msgs (whitespace := lax) in
example : Nat := _

/--
error: don't know how to synthesize implicit argument `α`
  @List.length ?m.2 []
context:
⊢ Type ?u.3
---
error: don't know how to synthesize implicit argument `α`
  @List.nil ?m.2
context:
⊢ Type ?u.3
-/
#guard_msgs (whitespace := lax) in
example : Nat := List.length []

/--
error: typeclass instance problem is stuck
  LE ?m.1

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LE` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (whitespace := lax) in
example : Prop := LE.le _ _

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : True := by
 have h := LE.le x x
 trivial

/--
error: typeclass instance problem is stuck
  LE ?m.3

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LE` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (whitespace := lax) in
example : True := by
 have h := LE.le _ _
 trivial

/--
error: typeclass instance problem is stuck
  LE ?m.2

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LE` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (whitespace := lax) in
example : Prop := by exact (LE.le _ _)

/--
error: typeclass instance problem is stuck
  LE ?m.2

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LE` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (whitespace := lax) in
example : Prop := by refine (LE.le _ _)

/--
error: typeclass instance problem is stuck
  LE ?m.2

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LE` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (whitespace := lax) in
example : Prop := by apply (LE.le _ _)

/--
error: typeclass instance problem is stuck
  LE ?m.2

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `LE` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (whitespace := lax) in
example : True := by
 have h : Prop := LE.le _ _
 trivial

/--
error: failed to synthesize instance of type class
  LT A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : Prop := (LE.le _ _) → x < x

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  LT A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : Prop := (x ≤ x) → x < x

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : Prop := by exact (x ≤ x)

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : Prop := by refine (x ≤ x)

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : Prop := by apply (LE.le x x)

/--
error: failed to synthesize instance of type class
  LE A

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (A : Type) (x : A) : True := by
 have h : Prop := (x ≤ x)
 trivial
