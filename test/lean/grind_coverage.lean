import Lean

namespace Coverage
structure Handle where
  id : Nat
  spin : Nat
  reachable : Bool
  touched : Bool
  dropped : Bool
structure Entity where
  id : Nat
  tokens : List Nat

def memq (x : Nat) : List Nat → Bool
  | [] => false
  | h :: t => if Nat.beq x h then true else memq x t

def coversOne (h : Handle) (e : Entity) : Bool :=
  if Nat.beq h.spin e.id then
    (if h.dropped then !(memq h.id e.tokens) else true) &&
    (if h.reachable && (h.touched && !h.dropped) then memq h.id e.tokens else true)
  else true

def covers (h : Handle) : List Entity → Bool
  | [] => true
  | e :: t => coversOne h e && covers h t

theorem covers_one_loss (h : Handle) (e : Entity) :
    coversOne h e = true → coversOne ⟨h.id, h.spin, false, h.touched, h.dropped⟩ e = true := by
  grind [coversOne]

theorem covers_loss (h : Handle) (es : List Entity) :
    covers h es = true → covers ⟨h.id, h.spin, false, h.touched, h.dropped⟩ es = true := by
  induction es
  · simp [covers]
  · intro hc
    grind [covers, covers_one_loss]
end Coverage
