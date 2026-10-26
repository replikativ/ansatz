-- New integration fixture, separate from the unchanged upstream corpus.
namespace JVMApplicationProbe

@[noinline] partial def sum64 (n acc : UInt64) : UInt64 :=
  if n == 0 then acc else sum64 (n - 1) (acc + n)

@[noinline] def entry (n acc : UInt64) : UInt64 := sum64 n acc
@[noinline] def identity64 (x : UInt64) : UInt64 := x

-- The host binding supplies this symbol; native execution requires a stub.
@[extern "ansatz_jvm_utf8_length"] opaque hostUtf8Length (s : String) : Nat :=
  s.utf8ByteSize

@[noinline] def callHost (s : String) : Nat := hostUtf8Length s

end JVMApplicationProbe
