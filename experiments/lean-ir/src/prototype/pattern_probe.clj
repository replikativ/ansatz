(ns prototype.pattern-probe
  "Optional Pattern dependency; shape validation only, not an LLVM importer."
  (:require [pattern.nanopass.dialect :refer [def-dialect valid?]]))

(defn llvm-type? [x] (contains? '#{i1 i32 i64} x))

(def-dialect LLVMScalar
  (terminals [v symbol?] [n integer?] [t llvm-type?])
  (Operand [a :enforce] ?v ?n)
  (Instruction [i :enforce]
               (assign ?v (add ?t ?a0 ?a1))
               (assign ?v (sub ?t ?a0 ?a1))
               (assign ?v (icmp eq ?t ?a0 ?a1))
               (assign ?v:result (call musttail tailcc ?t:return-type ?v:callee (args (?:* [?t:arg-type ?a:arg-value])))))
  (Terminator [k :enforce]
              (ret ?t ?a)
              (br ?v)
              (cbr ?a ?v0 ?v1))
  (Block [b :enforce]
         (block ?v (instructions (?:* i)) ?k))
  (Function [f :enforce]
            (define tailcc ?t:return-type ?v:function-name (params (?:* [?t:param-type ?v:param-name])) (blocks (?:+ b))))
  (Module [m :enforce] (llvm-module (?:+ f)))
  (entry Module))

(def sample
  '(llvm-module
    (define tailcc i64 count (params [i64 n] [i64 acc])
      (blocks
       (block entry (instructions (assign done (icmp eq i64 n 0))) (cbr done exit step))
       (block exit (instructions) (ret i64 acc))
       (block step (instructions
                    (assign next (sub i64 n 1))
                    (assign sum (add i64 acc 1))
                    (assign result (call musttail tailcc i64 count (args [i64 next] [i64 sum]))))
              (ret i64 result))))))

(defn check! []
  (let [valid (valid? LLVMScalar sample)
        invalid (valid? LLVMScalar '(llvm-module (define tailcc i64 bad (params) (blocks
                                     (block entry (instructions) (ret i64 1.5))))))]
    (assert valid "Pattern rejected the scalar LLVM-shaped CFG")
    (assert (not invalid) "Pattern accepted an out-of-profile operand")
    {:valid-sample valid :invalid-operand-rejected (not invalid)
     :scope :shape-only :importer-implemented false}))

(defn -main [& _]
  (println (check!))
  (shutdown-agents))
