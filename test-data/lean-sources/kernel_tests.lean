/-! Kernel test cases from lean4/tests/lean/run/kernel1.lean and kernel2.lean.
    Each `rfl` forces the kernel's isDefEq to verify the equality. -/
set_option linter.unusedVariables false

-- Nat arithmetic
theorem nat_add : (100 : Nat) + 100 = 200 := rfl
theorem nat_add_large : (100000000000 : Nat) + 100000000000 = 200000000000 := rfl
theorem nat_sub_zero : (100000000000 : Nat) - 100000000000 = 0 := rfl
theorem nat_mul : (12345 : Nat) * 6789 = 83810205 := rfl
theorem nat_mod : (100 : Nat) % 7 = 2 := rfl
theorem nat_div : (100 : Nat) / 7 = 14 := rfl
theorem nat_pow : (2 : Nat) ^ 10 = 1024 := rfl

-- Bool / decide
theorem decide_lt : decide ((100000000 : Nat) < 20000000000) = true := rfl
theorem decide_gt_false : decide ((20000000000 : Nat) > 200000000001) = false := rfl
theorem decide_eq : decide ((42 : Nat) = 42) = true := rfl
theorem decide_beq : ((42 : Nat) == 42) = true := rfl

-- String
theorem str_append : "hello" ++ "world" = "helloworld" := rfl
theorem str_length1 : "h".length = 1 := rfl
theorem str_length5 : "hello".length = 5 := rfl
theorem str_eq_false : decide ("hello" = "world") = false := rfl
theorem str_eq_true : decide ("hello" = "hello") = true := rfl

-- Char
theorem char_neq : decide (('a' : Char) = 'b') = false := rfl
theorem char_eq : decide (('a' : Char) = 'a') = true := rfl

-- List
theorem list_length : [1, 2, 3, 4, 5].length = 5 := rfl
theorem list_append : [1, 2] ++ [3, 4] = [1, 2, 3, 4] := rfl
theorem list_map : [1, 2, 3].map (· * 2) = [2, 4, 6] := rfl

-- Array
theorem array_size : #[1, 2, 3].size = 3 := rfl

-- Option
theorem option_some : (some 42 : Option Nat).get! = 42 := rfl

-- Structural: function application and reduction
def myId (x : Nat) := x
theorem myId_reduce : myId 42 = 42 := rfl

def myConst (x y : Nat) := x
theorem myConst_reduce : myConst 1 2 = 1 := rfl

-- Recursive definitions
def myFib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => myFib n + myFib (n + 1)
theorem fib_10 : myFib 10 = 55 := rfl

-- Structure projections
structure MyPair (α β : Type) where
  fst : α
  snd : β
theorem proj_fst : (MyPair.mk 1 2 : MyPair Nat Nat).fst = 1 := rfl
theorem proj_snd : (MyPair.mk 1 2 : MyPair Nat Nat).snd = 2 := rfl
