import Init

-- Lean 4 v4.33.1 oracle for Meta.Constructions, including nested auxiliary recursors.
namespace T10Reference
inductive Empty : Type
inductive Unit where
  | unit
inductive Enum where
  | a | b | c
inductive Rec where
  | z
  | s (n : Rec)
inductive Vec (a : Type) : Nat → Type where
  | nil : Vec a 0
  | cons (n : Nat) (x : a) (xs : Vec a n) : Vec a (Nat.succ n)
inductive Rose where
  | node (children : List Rose)
inductive Assoc (S : Type) where
  | mk (add : S → S → S)
       (assoc : ∀ a b c, add (add a b) c = add a (add b c))
inductive Disj (p q : Prop) : Prop where
  | left (h : p)
  | right (h : q)
inductive Spin where
  | pure (v : Nat)
  | await (id : Nat) (k : Nat → Spin)
  | yield (v : Nat) (k : Spin)
inductive Branch (A : Type) : Nat → Type where
  | leaf (n : Nat) : Branch A n
  | node (n : Nat) (k : ∀ (m : Nat), Fin (m + 1) → Branch A m) : Branch A n

def Spin.bind (s : Spin) (f : Nat → Spin) : Spin :=
  match s with
  | .pure v => f v
  | .await id k => .await id (fun x => (k x).bind f)
  | .yield v k => .yield v (k.bind f)

def Spin.run (fuel : Nat) (s : Spin) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 => match s with
    | .pure v => v
    | .await id k => (k id).run fuel
    | .yield _ k => k.run fuel

example (v : Nat) (f : Nat → Spin) : (Spin.pure v).bind f = f v := rfl
example : Spin.run 4 ((Spin.await 3 (fun x => .yield 9 (.pure x))).bind (fun x => .pure (x + 2))) = 5 := rfl

inductive Inf where
  | node (children : Nat → Inf)
mutual
  inductive Tree where
    | node (children : Forest)
  inductive Forest where
    | nil
    | cons (head : Tree) (tail : Forest)
end

-- Each proof consumes a generated construction.
example : Enum.a ≠ Enum.b := fun h => Enum.noConfusion h
example : ∀ a b : Rec, Rec.s a = Rec.s b → a = b :=
  fun _ _ h => Rec.s.noConfusion h (fun e => e)
example (v : Vec Nat 0) : Nat := Vec.casesOn v 0 (fun _ x _ => x)
noncomputable example (r : Rose) : Nat := @Rose.brecOn (fun _ => Nat) (fun _ => Nat) r (fun _ _ => 1) (fun _ _ => 1)
example (S : Type) (op₁ op₂ : S → S → S)
    (h₁ : ∀ a b c, op₁ (op₁ a b) c = op₁ a (op₁ b c))
    (h₂ : ∀ a b c, op₂ (op₂ a b) c = op₂ a (op₂ b c))
    (h : Assoc.mk op₁ h₁ = Assoc.mk op₂ h₂) : op₁ = op₂ :=
  Assoc.mk.noConfusion h (fun e => eq_of_heq e)
example (p q : Prop) (h : Disj p q) : p ∨ q :=
  Disj.casesOn h Or.inl Or.inr
end T10Reference
