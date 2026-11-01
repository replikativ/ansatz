import Lean.Expr

open Lean

def withMeta (xs : List (Name × DataValue)) (e : Expr) : Expr :=
  .mdata { entries := xs } e

def raw (s : String) (a b : Nat) : Substring.Raw :=
  { str := s, startPos := ⟨a⟩, stopPos := ⟨b⟩ }

def stx (info : SourceInfo) (text := "xx") : Syntax :=
  .node info `node #[.atom info text,
    .ident info (raw "_id_" 1 3) `id [.«namespace» `N, .decl `f ["x", "y"]]]

@[noinline] def spine (n : Nat) (e : Expr) : Expr :=
  n.fold (fun _ _ a => .app a e) e

@[noinline] def dag (n : Nat) (e : Expr) : Expr :=
  n.fold (fun _ _ a => .app a a) e

def check (label : String) (a b : Expr) (eqv equal : Bool) : IO Unit := do
  let actualEqv := a.eqv b
  let actualEqual := a.equal b
  unless actualEqv == eqv && actualEqual == equal do
    throw <| IO.userError s!"{label}: expected {eqv}/{equal}, got {actualEqv}/{actualEqual}"
  IO.println s!"{label}:{actualEqv}:{actualEqual}"

def main : IO Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let t := Expr.sort (.succ .zero)
  let z := Expr.bvar 0
  let lam := Expr.lam `x t z .default
  let renamed := Expr.lam `y t z .default
  let implicitLam := Expr.lam `x t z .implicit
  check "identity" lam lam true true
  check "bvar-equal" z (.bvar 0) true true
  check "bvar-different" z (.bvar 1) false false
  check "fvar-equal" (.fvar ⟨`f⟩) (.fvar ⟨`f⟩) true true
  check "fvar-different" (.fvar ⟨`f⟩) (.fvar ⟨`g⟩) false false
  check "mvar-equal" (.mvar ⟨`m⟩) (.mvar ⟨`m⟩) true true
  check "fvar-not-mvar" (.fvar ⟨`f⟩) (.mvar ⟨`f⟩) false false
  check "sort-zero-succ" (.sort .zero) t false false
  check "level-param" (.sort u) (.sort v) false false
  check "level-mvar" (.sort (.mvar ⟨`m⟩)) (.sort (.mvar ⟨`m⟩)) true true
  check "level-param-not-mvar" (.sort u) (.sort (.mvar ⟨`u⟩)) false false
  check "level-max-order" (.sort (.max u v)) (.sort (.max v u)) false false
  check "level-imax-structural" (.sort (.imax u v)) (.sort (.imax u v)) true true
  check "level-max-not-normalized" (.sort (.max u .zero)) (.sort u) false false
  check "const-level-list" (.const `c [u, v]) (.const `c [u, v]) true true
  check "const-level-order" (.const `c [u, v]) (.const `c [v, u]) false false
  check "const-level-length" (.const `c [u]) (.const `c [u, v]) false false
  check "const-name" (.const `c []) (.const `d []) false false
  check "app-argument" (.app lam z) (.app lam t) false false
  check "app-function" (.app lam z) (.app t z) false false
  check "lambda-name" lam renamed true false
  check "lambda-binder-info" lam implicitLam true false
  check "forall-name" (.forallE `x t z .default) (.forallE `y t z .default) true false
  check "forall-binder-info" (.forallE `x t z .default) (.forallE `x t z .instImplicit) true false
  check "lambda-not-forall" lam (.forallE `x t z .default) false false
  check "let-name" (.letE `x t t z false) (.letE `y t t z false) true false
  check "let-nondep" (.letE `x t t z false) (.letE `x t t z true) false false
  check "literal-nat-big" (.lit (.natVal (2^90+7))) (.lit (.natVal (2^90+7))) true true
  check "literal-nat-different" (.lit (.natVal (2^90+7))) (.lit (.natVal (2^90+8))) false false
  check "literal-string" (.lit (.strVal "λ😀\u0000x")) (.lit (.strVal "λ😀\u0000x")) true true
  check "literal-kind" (.lit (.natVal 1)) (.lit (.strVal "1")) false false
  check "proj-equal" (.proj `S 0 z) (.proj `S 0 z) true true
  check "proj-name" (.proj `S 0 z) (.proj `T 0 z) false false
  check "proj-index" (.proj `S 0 z) (.proj `S 1 z) false false
  check "metadata-not-erased" (withMeta [] z) z false false
  check "metadata-order" (withMeta [(`a, .ofNat 1), (`b, .ofNat 2)] z)
    (withMeta [(`b, .ofNat 2), (`a, .ofNat 1)] z) false false
  check "metadata-duplicate-length" (withMeta [(`a, .ofNat 1), (`a, .ofNat 1)] z)
    (withMeta [(`a, .ofNat 1)] z) false false
  check "metadata-key" (withMeta [(`a, .ofNat 1)] z) (withMeta [(`b, .ofNat 1)] z) false false
  check "metadata-string" (withMeta [(`a, .ofString "λ😀")] z) (withMeta [(`a, .ofString "λ😀")] z) true true
  check "metadata-bool" (withMeta [(`a, .ofBool false)] z) (withMeta [(`a, .ofBool true)] z) false false
  check "metadata-name" (withMeta [(`a, .ofName (.num `N 123))] z)
    (withMeta [(`a, .ofName (.num `N 123))] z) true true
  check "metadata-nat" (withMeta [(`a, .ofNat (2^100))] z) (withMeta [(`a, .ofNat (2^100))] z) true true
  check "metadata-int" (withMeta [(`a, .ofInt (-(2^100 : Int)))] z)
    (withMeta [(`a, .ofInt (-(2^100 : Int)))] z) true true
  check "metadata-int-sign" (withMeta [(`a, .ofInt (-9))] z) (withMeta [(`a, .ofInt 9)] z) false false
  check "metadata-nat-not-int" (withMeta [(`a, .ofNat 9)] z) (withMeta [(`a, .ofInt 9)] z) false false
  let info := SourceInfo.synthetic ⟨2⟩ ⟨7⟩ true
  check "syntax-sourceinfo" (withMeta [(`a, .ofSyntax (stx .none))] z)
    (withMeta [(`a, .ofSyntax (stx info))] z) true true
  check "syntax-atom" (withMeta [(`a, .ofSyntax (stx .none "a"))] z)
    (withMeta [(`a, .ofSyntax (stx .none "b"))] z) false false
  check "syntax-missing" (withMeta [(`a, .ofSyntax .missing)] z) (withMeta [(`a, .ofSyntax .missing)] z) true true
  let ident1 := Syntax.ident .none (raw "_id_" 1 3) `id []
  let ident2 := Syntax.ident info (raw "id" 0 2) `id []
  check "syntax-substring-content" (withMeta [(`a, .ofSyntax ident1)] z) (withMeta [(`a, .ofSyntax ident2)] z) true true
  check "syntax-preresolved" (withMeta [(`a, .ofSyntax ident1)] z)
    (withMeta [(`a, .ofSyntax (.ident .none (raw "id" 0 2) `id [.decl `f ["x"]]))] z) false false
  check "syntax-preresolved-order" (withMeta [(`a, .ofSyntax (.ident .none (raw "id" 0 2) `id [.«namespace» `A, .«namespace» `B]))] z)
    (withMeta [(`a, .ofSyntax (.ident .none (raw "id" 0 2) `id [.«namespace» `B, .«namespace» `A]))] z) false false
  check "syntax-substring-repair" (withMeta [(`a, .ofSyntax (.ident .none (raw "λ" 1 2) `id []))] z)
    (withMeta [(`a, .ofSyntax (.ident .none (raw "" 0 0) `id []))] z) true true
  check "deep-app-spine" (spine 4096 lam) (spine 4096 renamed) true false
  check "shared-dag" (dag 22 lam) (dag 22 renamed) true false
