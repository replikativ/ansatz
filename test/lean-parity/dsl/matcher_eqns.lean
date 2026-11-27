/-
Pairs with: ansatz.matcher-eqns-test
Observed with Lean v4.36.0 (core only), Meta/Match/MatchEqs.lean:
- matcher equations quantify over the matcher's own binders: parameters with their kinds (`{n}`
  `{α}` implicit), `motive`, the pattern variables by name, the alternatives `h_1 h_2 …`;
- an overlapped alternative's equation has the precedence hypothesis;
- `match_1.congr_eq_i` states the alternative for an arbitrary discriminant equal to the pattern,
  as an `HEq`, with the same hypotheses.
-/
inductive T where | a (n : Nat) | b
def f : T → Nat
  | .a n => n
  | _ => 0
/--
info: f.match_1.eq_1 : ∀ (motive : T → Sort u_1) (n : Nat) (h_1 : (n : Nat) → motive (T.a n)) (h_2 : (x : T) → motive x),
  (match T.a n with
    | T.a n => h_1 n
    | x => h_2 x) =
    h_1 n
-/
#guard_msgs in #check @f.match_1.eq_1
/--
info: f.match_1.congr_eq_1 : ∀ (motive : T → Sort u_1) (x : T) (h_1 : (n : Nat) → motive (T.a n)) (h_2 : (x : T) → motive x)
  (n : Nat),
  x = T.a n →
    (match x with
      | T.a n => h_1 n
      | x => h_2 x) ≍
      h_1 n
-/
#guard_msgs in #check @f.match_1.congr_eq_1
/--
info: f.match_1.congr_eq_2 : ∀ (motive : T → Sort u_1) (x : T) (h_1 : (n : Nat) → motive (T.a n)) (h_2 : (x : T) → motive x)
  (x_1 : T),
  x = x_1 →
    (∀ (n : Nat), x_1 = T.a n → False) →
      (match x with
        | T.a n => h_1 n
        | x => h_2 x) ≍
        h_2 x_1
-/
#guard_msgs in #check @f.match_1.congr_eq_2

inductive V (α : Type) : Nat → Type where
  | nil : V α 0
  | cons {n} (x : α) (xs : V α n) : V α (n+1)
def g {α} : V α (n+1) → α
  | .cons x _ => x
/--
info: @g.match_1.eq_1 : ∀ {n : Nat} {α : Type} (motive : V α (n + 1) → Sort u_1) (x : α) (xs : V α n)
  (h_1 : (x : α) → (xs : V α n) → motive (V.cons x xs)),
  (match V.cons x xs with
    | V.cons x xs => h_1 x xs) =
    h_1 x xs
-/
#guard_msgs in #check @g.match_1.eq_1
