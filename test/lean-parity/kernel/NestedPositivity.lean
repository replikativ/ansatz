/-
Nested positivity (K4 audit finding 4). Lean copies the container into the auxiliary
mutual block, so a container that uses its parameter contravariantly exposes the negative
occurrence. A covariant container is accepted.
-/
inductive Contra (α : Type) where
  | mk : (α → Nat) → Contra α

/-- error: (kernel) arg #1 of '_nested.Contra_1.mk' has a non positive occurrence of the datatypes being declared -/
#guard_msgs in
inductive Bad where
  | mk : Contra Bad → Bad

inductive Box (α : Type) where
  | mk : α → Box α

inductive Good where
  | mk : Box Good → Good

/-- info: Good.rec_1.{u} {motive_1 : Good → Sort u} {motive_2 : Box Good → Sort u}
  (mk : (a : Box Good) → motive_2 a → motive_1 (Good.mk a)) :
  ((a : Good) → motive_1 a → motive_2 (Box.mk a)) → (t : Box Good) → motive_2 t -/
#guard_msgs in
#check Good.rec_1

-- a negative occurrence through the mutual sibling is rejected too (finding 3)
/-- error: (kernel) arg #1 of 'B.mk' has a non positive occurrence of the datatypes being declared -/
#guard_msgs in
mutual
inductive A where
  | mk : B → A
inductive B where
  | mk : (B → Nat) → B
end
