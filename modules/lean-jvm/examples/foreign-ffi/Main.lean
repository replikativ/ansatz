import Bindings

namespace HostInterop

def useLength (text : String) : Nat := length text
def useMessage (n : Nat) (enabled : Bool) : Message := makeMessage n enabled
def useZero (_ : Nat) : Nat := zero

def describe (key : String) : IO String := do
  try
    readConfig key
  catch error =>
    pure ("caught:" ++ error.toString)

def runReference (key : String) : IO String := referenceRead key

end HostInterop
