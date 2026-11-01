module
public import Init
public initialize runtimeRef : IO.Ref Nat ← IO.mkRef 23
public meta initialize compileRef : IO.Ref Nat ← IO.mkRef 29
