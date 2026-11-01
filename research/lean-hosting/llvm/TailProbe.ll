; Bounded plumbing experiment for a future Pattern/LLVM dialect.
; i64 bit-vector arithmetic, not general Lean Nat or the guest heap ABI.
define tailcc i64 @count(i64 %n, i64 %acc) {
entry:
  %done = icmp eq i64 %n, 0
  br i1 %done, label %exit, label %step
exit:
  ret i64 %acc
step:
  %next = sub i64 %n, 1
  %sum = add i64 %acc, 1
  %result = musttail call tailcc i64 @count(i64 %next, i64 %sum)
  ret i64 %result
}

define i32 @main() {
entry:
  %answer = call tailcc i64 @count(i64 200000, i64 0)
  %correct = icmp eq i64 %answer, 200000
  %status = select i1 %correct, i32 0, i32 1
  ret i32 %status
}
