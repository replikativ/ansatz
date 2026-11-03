namespace Domain
structure Account where
  balance : Nat
  enabled : Bool
  deriving Inhabited

@[noinline] def credit (account : Account) (amount : Nat) : Account :=
  { account with balance := account.balance + amount }
theorem credit_balance (a : Account) (n : Nat) : (credit a n).balance = a.balance + n := rfl
initialize bonus : Nat ← pure 3
end Domain
