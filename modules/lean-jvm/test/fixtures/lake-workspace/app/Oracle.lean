import App

def main : IO Unit := do
  IO.println (App.calculate 32)
  let account := App.account 35
  IO.println s!"{account.balance},{account.enabled}"
