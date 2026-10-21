import Init

def main : IO Unit :=
  IO.println (repr (List.map (fun (n : Nat) => n + 1) [1, 2, 3, 4]))
