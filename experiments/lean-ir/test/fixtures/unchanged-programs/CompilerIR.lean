/-!
# Backend-neutral typed finite command IR

This IR describes finite sampler control flow without Julia syntax or indexing
conventions. Array indices are zero-based, matching Lean `Fin` values and trace
semantics. Backends are responsible for lowering that convention explicitly.
-/

namespace Mcmc.Executable.Finite.CompilerIR

inductive Ty where
  | source | nat | bool | natVector | natMatrix

structure Var (type : Ty) where
  name : String

inductive Expr : Ty → Type
  | var (value : Var type) : Expr type
  | nat (value : Nat) : Expr .nat
  | vector (values : List Nat) : Expr .natVector
  | matrix (rows : List (List Nat)) : Expr .natMatrix
  | add (left right : Expr .nat) : Expr .nat
  | sub (left right : Expr .nat) : Expr .nat
  | mul (left right : Expr .nat) : Expr .nat
  | min (left right : Expr .nat) : Expr .nat
  | length (value : Expr .natVector) : Expr .nat
  | rowCount (value : Expr .natMatrix) : Expr .nat
  | total (value : Expr .natVector) : Expr .nat
  | index (value : Expr .natVector) (index : Expr .nat) : Expr .nat
  | row (value : Expr .natMatrix) (index : Expr .nat) : Expr .natVector
  | lt (left right : Expr .nat) : Expr .bool
  | le (left right : Expr .nat) : Expr .bool
  | eq (left right : Expr .nat) : Expr .bool
  | and (left right : Expr .bool) : Expr .bool
  | allNonnegative (value : Expr .natVector) : Expr .bool
  | allPositive (value : Expr .natVector) : Expr .bool
  | allRowsLength (value : Expr .natMatrix) (size : Expr .nat) : Expr .bool
  | allRowsNonnegativePositive (value : Expr .natMatrix) : Expr .bool
  | toExactVector (value : Expr .natVector) : Expr .natVector
  | toExactMatrix (value : Expr .natMatrix) : Expr .natMatrix
  | categorical (source : Expr .source) (weights : Expr .natVector) : Expr .nat

inductive Failure where
  | argument (message : String)
  | dimension (message : String)
  | internal (message : String)
  deriving DecidableEq, Repr

inductive Stmt where
  | letE (destination : Var type) (value : Expr type)
  | guard (condition : Expr .bool) (failure : Failure)
  | drawBelow (destination : Var .nat) (source : Expr .source) (upper : Expr .nat)
  | ifThen (condition : Expr .bool) (body : List Stmt)
  | return (value : Expr .nat)
  | fail (failure : Failure)

structure Input where
  type : Ty
  name : String

structure Program where
  name : String
  inputs : List Input
  body : List Stmt

def sourceVar : Var .source := ⟨"source"⟩
def weightsVar : Var .natVector := ⟨"weights"⟩
def targetVar : Var .natVector := ⟨"target"⟩
def proposalVar : Var .natMatrix := ⟨"proposal"⟩
def currentVar : Var .nat := ⟨"current"⟩
def proposedVar : Var .nat := ⟨"proposed"⟩
def drawVar : Var .nat := ⟨"draw"⟩

def mhCurrentRow : Expr .natVector := .row (.var proposalVar) (.var currentVar)
def mhProposedRow : Expr .natVector := .row (.var proposalVar) (.var proposedVar)
def mhUpper : Expr .nat := .mul
  (.mul (.index (.var targetVar) (.var currentVar))
    (.index mhCurrentRow (.var proposedVar)))
  (.total mhProposedRow)
def mhThreshold : Expr .nat := .min mhUpper
  (.mul (.mul (.index (.var targetVar) (.var proposedVar))
    (.index mhProposedRow (.var currentVar))) (.total mhCurrentRow))

/-- Categorical primitive entry point in backend-neutral control flow. -/
def categoricalProgram : Program where
  name := "categorical_index!"
  inputs := [⟨.source, sourceVar.name⟩, ⟨.natVector, weightsVar.name⟩]
  body :=
    let selected : Var .nat := ⟨"selected"⟩
    [.letE selected (.categorical (.var sourceVar) (.var weightsVar)),
      .return (.var selected)]

/-- Generic exact finite MH statement list. -/
def metropolisHastingsBody : List Stmt :=
    [.letE proposedVar (.categorical (.var sourceVar)
        (.row (.var proposalVar) (.var currentVar))),
      .ifThen (.eq (.var proposedVar) (.var currentVar)) [.return (.var currentVar)],
      .drawBelow drawVar (.var sourceVar) mhUpper,
      .ifThen (.lt (.var drawVar) mhThreshold) [.return (.var proposedVar)],
      .return (.var currentVar)]

/-- Generic exact finite MH control flow. -/
def metropolisHastingsProgram : Program where
  name := "finite_mh_step!"
  inputs := [⟨.source, sourceVar.name⟩, ⟨.natVector, targetVar.name⟩,
    ⟨.natMatrix, proposalVar.name⟩, ⟨.nat, currentVar.name⟩]
  body := metropolisHastingsBody

/-- Concrete literals used by the backend's thin two-state wrapper. -/
def twoStateTarget : Expr .natVector := .vector [1, 3]
def twoStateProposal : Expr .natMatrix := .matrix [[1, 1], [1, 1]]

end Mcmc.Executable.Finite.CompilerIR
