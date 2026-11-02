def readBytes (n : USize) : IO ByteArray := do
  (← IO.getStdin).read n

def readLine : IO String := do
  (← IO.getStdin).getLine

def echoBytes : IO Unit := do
  let input ← (← IO.getStdin).read 32
  (← IO.getStdout).write input

def splitUtf8 : IO Unit := do
  let out ← IO.getStdout
  out.write (ByteArray.mk #[0xf0, 0x9f])
  out.write (ByteArray.mk #[0x98, 0x80])

def invalidUtf8 : IO Unit := do
  (← IO.getStdout).write (ByteArray.mk #[0xc0, 0x80])

def wrongDirectionCaught : IO Bool := do
  try
    let _ ← (← IO.getStdout).read 1
    pure false
  catch _ => pure true

def message : IO Unit := IO.println "hello"
def errorMessage : IO Unit := IO.eprintln "error"

def main : IO Unit := echoBytes
