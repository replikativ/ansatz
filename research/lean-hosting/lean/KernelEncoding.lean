import Lean
open Lean
namespace KernelEncoding

-- Object-only host inputs. All caches in the OUTPUT are computed by the real
-- Lean constructors below, never by copying Java hashes or packed Expr.data.
structure NodeInput where
  kind : Nat
  number : Nat
  text : String
  args : Array Nat
  original : Option Expr
structure RuleInput where
  ctor : Nat
  fields : Nat
  rhs : Nat
structure ConstantInput where
  kind : Nat
  name : Nat
  levels : Array Nat
  type : Nat
  all : Array Nat
  parent : Nat
  numbers : Array Nat
  ctors : Array Nat
  flags : Array Nat
  rules : Array RuleInput

private def indexValue (xs : Array α) (index : Nat) : Except String α :=
  match xs[index]? with
  | some value => pure value
  | none => throw "KernelEncoding index out of bounds"
private def arity (args : Array Nat) (n : Nat) : Except String Unit :=
  if args.size == n then pure () else throw "KernelEncoding node arity mismatch"
private def flag (n : Nat) : Except String Bool :=
  if n == 0 then pure false else if n == 1 then pure true else throw "KernelEncoding invalid Bool"
private def binder (n : Nat) : Except String BinderInfo :=
  match n with
  | 0 => pure .default
  | 1 => pure .implicit
  | 2 => pure .strictImplicit
  | 3 => pure .instImplicit
  | _ => throw "KernelEncoding invalid BinderInfo"

private def decodeNameTable (nameInputs : Array NodeInput) : Except String (Array Name) := do
  let mut names : Array Name := #[]
  for input in nameInputs do
    let value ← match input.kind with
      | 0 => arity input.args 0 *> pure Name.anonymous
      | 1 => do
        arity input.args 1
        pure <| Name.str (← indexValue names (← indexValue input.args 0)) input.text
      | 2 => do
        arity input.args 1
        pure <| Name.num (← indexValue names (← indexValue input.args 0)) input.number
      | _ => throw "KernelEncoding invalid Name kind"
    names := names.push value
  return names

/-- Faithful Name construction without parsing a dotted string or copying
Java cache values. Root indices allow shared prefixes and numeric components. -/
@[noinline] def decodeNames (inputs : Array NodeInput) (roots : Array Nat) : Except String (Array Name) := do
  let names ← decodeNameTable inputs
  roots.mapM (indexValue names)

/-- Audited guest reconstruction of a previously strictly checked Java family.
This is NOT admission. The host must reproject every CI and compare the complete
family to its checked Java result before passing it to a publication helper.
Original source type roots can be reused exactly, with guest ownership intact. -/
@[noinline] def decodeFamily (nameInputs levelInputs exprInputs : Array NodeInput)
    (constantInputs : Array ConstantInput) : Except String (Array ConstantInfo) := do
  let names ← decodeNameTable nameInputs
  let mut levels : Array Level := #[]
  for input in levelInputs do
    let value ← match input.kind with
      | 0 => arity input.args 0 *> pure Level.zero
      | 1 => do
        arity input.args 1
        pure <| mkLevelSucc (← indexValue levels (← indexValue input.args 0))
      | 2 => do
        arity input.args 2
        pure <| mkLevelMax (← indexValue levels (← indexValue input.args 0)) (← indexValue levels (← indexValue input.args 1))
      | 3 => do
        arity input.args 2
        pure <| mkLevelIMax (← indexValue levels (← indexValue input.args 0)) (← indexValue levels (← indexValue input.args 1))
      | 4 => do
        arity input.args 1
        pure <| mkLevelParam (← indexValue names (← indexValue input.args 0))
      | _ => throw "KernelEncoding invalid Level kind"
    levels := levels.push value
  let mut expressions : Array Expr := #[]
  for input in exprInputs do
    let value ← if let some original := input.original then do
        unless input.kind == 99 do throw "KernelEncoding original Expr marker mismatch"
        arity input.args 0
        pure original
      else match input.kind with
      | 0 => arity input.args 0 *> pure (mkBVar input.number)
      | 1 => do
        arity input.args 1
        pure <| mkSort (← indexValue levels (← indexValue input.args 0))
      | 2 => do
        unless !input.args.isEmpty do throw "KernelEncoding constant missing Name"
        let name ← indexValue names (← indexValue input.args 0)
        let us ← (input.args.extract 1 input.args.size).mapM (indexValue levels)
        pure <| mkConst name us.toList
      | 3 => do
        arity input.args 2
        pure <| mkApp (← indexValue expressions (← indexValue input.args 0)) (← indexValue expressions (← indexValue input.args 1))
      | 4 | 5 => do
        arity input.args 3
        let name ← indexValue names (← indexValue input.args 0)
        let type ← indexValue expressions (← indexValue input.args 1)
        let body ← indexValue expressions (← indexValue input.args 2)
        let bi ← binder input.number
        pure <| if input.kind == 4 then mkLambda name bi type body else mkForall name bi type body
      | 6 => do
        arity input.args 4
        pure <| mkLet (← indexValue names (← indexValue input.args 0)) (← indexValue expressions (← indexValue input.args 1))
          (← indexValue expressions (← indexValue input.args 2)) (← indexValue expressions (← indexValue input.args 3)) (← flag input.number)
      | 7 => arity input.args 0 *> pure (mkNatLit input.number)
      | 8 => arity input.args 0 *> pure (mkStrLit input.text)
      | 10 => do
        arity input.args 2
        pure <| mkProj (← indexValue names (← indexValue input.args 0)) input.number (← indexValue expressions (← indexValue input.args 1))
      | _ => throw "KernelEncoding invalid/unimplemented Expr kind"
    expressions := expressions.push value
  let mut constants := #[]
  for input in constantInputs do
    let name ← indexValue names input.name
    let params ← input.levels.mapM (indexValue names)
    let type ← indexValue expressions input.type
    let all ← input.all.mapM (indexValue names)
    let value ← match input.kind with
      | 5 => do
        arity input.numbers 3
        arity input.flags 3
        let ctors ← input.ctors.mapM (indexValue names)
        pure <| ConstantInfo.inductInfo {
          name, levelParams := params.toList, type, all := all.toList, ctors := ctors.toList,
          numParams := (← indexValue input.numbers 0), numIndices := (← indexValue input.numbers 1),
          numNested := (← indexValue input.numbers 2), isRec := (← flag (← indexValue input.flags 0)),
          isUnsafe := (← flag (← indexValue input.flags 1)), isReflexive := (← flag (← indexValue input.flags 2)) }
      | 6 => do
        arity input.numbers 3
        arity input.flags 1
        pure <| ConstantInfo.ctorInfo {
          name, levelParams := params.toList, type, induct := (← indexValue names input.parent),
          cidx := (← indexValue input.numbers 0), numParams := (← indexValue input.numbers 1),
          numFields := (← indexValue input.numbers 2), isUnsafe := (← flag (← indexValue input.flags 0)) }
      | 7 => do
        arity input.numbers 4
        arity input.flags 2
        let rules ← input.rules.mapM fun rule => do
          pure ({ctor := (← indexValue names rule.ctor), nfields := rule.fields,
                 rhs := (← indexValue expressions rule.rhs)} : RecursorRule)
        pure <| ConstantInfo.recInfo {
          name, levelParams := params.toList, type, all := all.toList,
          numParams := (← indexValue input.numbers 0), numIndices := (← indexValue input.numbers 1),
          numMotives := (← indexValue input.numbers 2), numMinors := (← indexValue input.numbers 3),
          rules := rules.toList, k := (← flag (← indexValue input.flags 0)), isUnsafe := (← flag (← indexValue input.flags 1)) }
      | _ => throw "KernelEncoding invalid generated ConstantInfo kind"
    constants := constants.push value
  return constants
end KernelEncoding
