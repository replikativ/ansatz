import WriterLib

-- Exactly the same application and arguments as Main; the harness records final files.
def main (args : List String) : IO UInt32 := runWriter args
