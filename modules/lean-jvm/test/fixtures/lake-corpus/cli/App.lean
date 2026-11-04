import Cli
namespace CliProbe

def command := `[Cli|
  probe NOOP;
  "JVM compatibility probe."
  FLAGS:
    verbose; "Enable verbose output."
  ARGS:
    input : String; "Input label."
]

def parse (args : List String) : Except String Bool := do
  let (_, parsed) ← command.parse args |>.mapError (fun _ => "invalid arguments")
  pure (parsed.hasFlag "verbose")

def matchNumbers (xs ys : List Nat) : List Nat × List Nat :=
  Cli.List.matchLength xs ys 0
end CliProbe
