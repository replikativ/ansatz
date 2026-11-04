import Lean

structure RewriteOut where
  wv : Nat
  ok : Bool
structure RewriteNested where
  out : RewriteOut

example (x : RewriteOut) (h : x = ⟨0, false⟩) : x.wv = 0 := by rw [h]
example (x : RewriteNested) (h : x = ⟨⟨0, false⟩⟩) : x.out.wv = 0 := by rw [h]
example (x : RewriteOut) (h : x = ⟨0, false⟩) (hx : x.wv = 7) : 0 = 7 := by
  rw [h] at hx
  exact hx

example (x : RewriteOut) (_h : x = ⟨0, false⟩) : (0 : Nat) = 0 := by
  fail_if_success rw [_h]
  rfl
example (x : RewriteOut) (_h : x = ⟨0, false⟩) (hx : (0 : Nat) = 0) : (0 : Nat) = 0 := by
  fail_if_success rw [_h] at hx
  exact hx

def rewriteOutF (n : Nat) : RewriteOut := ⟨n, true⟩
example (n : Nat) (h : rewriteOutF n = ⟨0, false⟩) : (rewriteOutF n).wv = 0 := by rw [h]
example (n m : Nat) (h : n = m) : n = n := by
  rewrite (occs := .pos [2]) [h]
  exact h

example (n : Nat) (h : rewriteOutF n = ⟨0, false⟩) (hx : (rewriteOutF n).wv = 7) : 0 = 7 := by
  rw [h] at hx
  exact hx

example (_h : ∀ n : Nat, Nat.succ n = n) : (0 : Nat) = 0 := by
  fail_if_success rw [_h]
  rfl
example (n m : Nat) (h : n = m) (hx : n = n) : n = m := by
  rewrite (occs := .pos [2]) [h] at hx
  exact hx

example {α : Type} (l : List α)
    (h : ∀ acc, l.foldl (fun a y => y :: a) acc = l.reverse ++ acc) :
    l.foldl (fun a y => y :: a) [] = l.reverse := by
  rw [h]
  exact List.append_nil l.reverse

example {S : Type} (op : S → S → S)
    (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (a b c : S) :
    op a (op b c) = op (op a b) c := by
  simp only [assoc]

example (rule : ∀ n : Nat, Nat.succ n = 0) :
    Nat.succ 1 + Nat.succ 2 = Nat.succ 1 + 0 := by
  rewrite (occs := .pos [2]) [rule]
  rfl
