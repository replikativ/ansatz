import Lean.Expr
open Lean

def withMeta (xs : List (Name × DataValue)) (e : Expr) : Expr :=
  .mdata { entries := xs } e

def check (label : String) (a b : Expr) (ab ba : Bool) : IO Unit := do
  let x := a.quickLt b
  let y := b.quickLt a
  unless x == ab && y == ba do
    throw <| IO.userError s!"{label}: expected {ab}/{ba}, got {x}/{y}"
  IO.println s!"{label}:{x}:{y}"

def main : IO Unit := do
  let z := Expr.bvar 0
  let t := Expr.sort .zero
  check "identity" z z false false
  check "kind-before-hash" z (.fvar ⟨`x⟩) true false
  let la := Expr.lam `x t z .default
  let lb := Expr.lam `y t z .implicit
  check "eqv-binder" la lb false false
  check "lambda-before-forall" la (.forallE `x t z .default) true false
  check "let-name-ignored" (.letE `x t t z false) (.letE `y t t z false) false false
  let md := fun v => withMeta [(`k, v)] z
  check "metadata-string" (md (.ofString "a")) (md (.ofString "b")) true false
  check "metadata-null-byte" (md (.ofString "a\u0000b")) (md (.ofString "a\u0000c")) true false
  check "metadata-utf8" (md (.ofString "\uE000")) (md (.ofString "𐀀")) true false
  check "metadata-bool" (md (.ofBool false)) (md (.ofBool true)) true false
  check "metadata-name-num-before-str" (md (.ofName (.num `P 9))) (md (.ofName (.str `P "0"))) true false
  check "metadata-key-num-before-str" (withMeta [(.num `P 9, .ofNat 0)] z)
    (withMeta [(.str `P "0", .ofNat 0)] z) true false
  check "metadata-key-prefix" (withMeta [(`P, .ofNat 0)] z)
    (withMeta [(.num `P 0, .ofNat 0)] z) true false
  check "metadata-nat-large" (md (.ofNat (2^90))) (md (.ofNat (2^100))) true false
  let intA := md (.ofInt (-9))
  let intB := md (.ofInt 9)
  check "metadata-int-incomparable" intA intB false false
  let syntaxA := md (.ofSyntax .missing)
  let syntaxB := md (.ofSyntax (.atom .none "x"))
  check "metadata-syntax-incomparable" syntaxA syntaxB false false
  check "metadata-int-then-tail" (withMeta [(`k, .ofInt (-9)), (`tail, .ofNat 1)] z)
    (withMeta [(`k, .ofInt 9), (`tail, .ofNat 2)] z) true false
  check "metadata-syntax-then-tail" (withMeta [(`k, .ofSyntax .missing), (`tail, .ofBool false)] z)
    (withMeta [(`k, .ofSyntax (.atom .none "x")), (`tail, .ofBool true)] z) true false
  check "metadata-list-order" (withMeta [(`a, .ofNat 1), (`b, .ofNat 2)] z)
    (withMeta [(`b, .ofNat 2), (`a, .ofNat 1)] z) true false
  check "metadata-duplicate-tail" (withMeta [(`k, .ofNat 1)] z)
    (withMeta [(`k, .ofNat 1), (`k, .ofNat 1)] z) true false
  IO.println s!"genuine-metadata-hash:{intA.hash == intB.hash && !(intA.eqv intB)}"
  let appA := Expr.app intA (md (.ofString "a"))
  let appB := Expr.app intB (md (.ofString "b"))
  check "app-no-incomparable-fallthrough" appA appB false false
  IO.println s!"genuine-app-hash:{appA.hash == appB.hash}"
  check "mdata-no-incomparable-fallthrough" (withMeta [(`outer, .ofNat 1)] intA)
    (withMeta [(`outer, .ofNat 2)] intB) false false
  let projA := Expr.proj `S 0 intA
  let projB := Expr.proj `S (2^64) intB
  check "proj-no-incomparable-fallthrough" projA projB false false
  IO.println s!"genuine-proj-hash:{projA.hash == projB.hash}"
