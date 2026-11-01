(ns java-ir-pointer-hash-followup-checks
  "Original traversal oracle cases and late pointer-table continuation gates."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [clojure.string :as str] [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-pointer-hash-checks :as p] [java-ir-pointer-checks :as pointer]
            [java-ir-expr-machinery-checks :as expr] [java-ir-host-checks :as h]
            [java-ir-code-checks :as code] [java-ir-generation-checks :as g]))
(def ^:dynamic *basis* nil)
(def pv h/private-value)
(defn context ([] (context {})) ([options] (binding [p/*basis* *basis*] (p/context options))))
(defn name! [ctx e s] (p/call ctx e "Lean.Name.str._override" [0 s]))
(defn app! [ctx e a b] (p/call ctx e "Lean.Expr.app._override" [a b]))
(defn name-text [ctx n] (if (= n 0) "" (second (p/fields ctx n))))
(defn names-text [ctx a] (str/join "," (map #(name-text ctx %) (take (.arraySize a) (p/fields ctx a)))))
(defn setup-rows []
  [(c/decl "model-level-list" [(c/p 1 "object") (c/p 2 "object")] "object"
     (c/let-ir 3 "object" (c/ctor 1 [(c/v 1) (c/v 2)] 0) (c/ret 3)))
   (c/decl "model-nat-literal" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
   (c/decl "model-string-literal" [(c/p 1 "object")] "object"
     (c/let-ir 2 "object" (c/ctor 1 [(c/v 1)] 0) (c/ret 2)))])
(defn shared! [ctx e]
  (let [sub (app! ctx e (p/constant! ctx e "A") (p/constant! ctx e "B"))]
    (app! ctx e (p/retain ctx e sub) (app! ctx e sub (p/constant! ctx e "A")))))
(defn forms! [ctx e]
  (let [a (p/constant! ctx e "A") b (p/constant! ctx e "B") c (p/constant! ctx e "C")
        lambda (p/call ctx e "Lean.Expr.lam._override._boxed" [(name! ctx e "y") (p/retain ctx e b) (p/retain ctx e c) 1])
        binding (p/call ctx e "Lean.Expr.forallE._override._boxed" [(name! ctx e "x") (p/retain ctx e a) lambda 0])
        let-value (p/call ctx e "Lean.Expr.letE._override._boxed" [(name! ctx e "z") a b c 1])
        projection (p/call ctx e "Lean.Expr.proj._override" [(name! ctx e "Struct") 1 let-value])]
    (p/call ctx e "Lean.Expr.mdata._override" [0 (app! ctx e binding projection)])))
(defn levels! [ctx e]
  (let [level (p/call ctx e "Lean.Level.param._override" [(name! ctx e "universe")])
        levels (p/call ctx e "model-level-list" [level 0])]
    (p/call ctx e "Lean.Expr.const._override" [(name! ctx e "UniverseConst") levels])))
(defn leaves! [ctx e]
  (let [leaves [(p/bvar! ctx e 0)
                (p/call ctx e "Lean.Expr.fvar._override" [(name! ctx e "free")])
                (p/call ctx e "Lean.Expr.mvar._override" [(name! ctx e "meta")])
                (p/call ctx e "Lean.Expr.sort._override" [(p/call ctx e "Lean.Level.param._override" [(name! ctx e "u")])])
                (p/call ctx e "Lean.Expr.lit._override" [(p/call ctx e "model-nat-literal" [42])])
                (p/call ctx e "Lean.Expr.lit._override" [(p/call ctx e "model-string-literal" ["text"])])]]
    (reduce #(app! ctx e %1 %2) (p/call ctx e "Lean.Expr.sort._override" [0]) leaves)))
(defn dag! [ctx e]
  (loop [n 12 value (p/constant! ctx e "A")]
    (if (zero? n) value (recur (dec n) (app! ctx e (p/retain ctx e value) value)))))
(deftest jvm-original-routes-match-the-fifteen-observed-native-semantic-lines
  (let [{:keys [ctx] :as lab} (context {:rows (setup-rows)}) e (p/engine lab)
        observed (atom [])]
    (doseq [[label build] [["shared-and-equal" shared!] ["binding-let-mdata-proj" forms!]
                           ["levels" levels!] ["nonconstant-leaves" leaves!] ["repeated-dag" dag!]]]
      (let [input (build ctx e)]
        (doseq [mode ["used" "used-again" "callback"]]
          (let [result (if (= mode "callback")
                         (p/call ctx e "Lean.Expr.FoldConstsImpl.foldUnsafe._redArg"
                           [(p/retain ctx e input) (p/call ctx e "Array.mkEmpty" [0 0])
                            (j/make-closure! ctx e "Lean.Expr.getUsedConstants._lam_0" [])])
                         (p/call ctx e "Lean.Expr.getUsedConstants" [(p/retain ctx e input)]))]
            (swap! observed conj (str label ":" mode "=" (names-text ctx result))) (j/release! ctx e result)))
        (j/release! ctx e input)))
    (is (= (str/split-lines (slurp (str p/directory "native.stdout"))) @observed))
    (let [seed (p/seed! ctx e)] (is (= 0 (p/size ctx seed))) (j/release! ctx e seed)) (j/close! ctx e)))
(defn host-request! [ctx e]
  (expr/until! ctx e #(some? (j/host-request ctx e))) (j/host-request ctx e))
(deftest original-fold-callback-code-then-host-fork-preserves-observed-table
  (if-not (:explicit *basis*) (is true "Source callback suspension is explicit-driver only")
    (let [event (h/spec "model_fold_observe" ["tobject"] [true] "object")
          callback (c/decl "model-fold-callback" [(c/p 1 "tobject") (c/p 2 "object")] "object"
                     (c/let-ir 3 "object" (c/fap "model-fold-observe" [(c/v 1)])
                       (c/let-ir 4 "object" (p/raw "Array.push" ["erased" (c/v 2) (c/v 1)]) (c/ret 4))))
          {:keys [ctx headers] :as lab} (context {:rows [(h/ext "model-fold-observe" event) callback]
                                                 :host-specs [event] :defer #{"model-fold-callback"}})
          parent (p/engine lab) input (shared! ctx parent)
          init (p/call ctx parent "Array.mkEmpty" [0 0]) closure (j/make-closure! ctx parent "model-fold-callback" [])]
      (j/start! ctx parent "Lean.Expr.FoldConstsImpl.foldUnsafe._redArg" [input init closure])
      (expr/constructor-request! ctx parent)
      (let [request (j/code-request ctx parent) {:keys [engine roots]} (j/fork! ctx parent [input]) child engine ci (first roots)
            ready (expr/materialize lab "model-fold-callback")]
        (is (identical? (headers "model-fold-callback") (.header request)))
        (is (= (pointer/word input) (pointer/word ci)))
        (doseq [e [parent child]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [a (host-request! ready e)] (is (= "A" (name-text ready (first (h/args a)))))
            (is (g/bad? #(j/resume-host! ready e a (Double/valueOf 0.5)))) (is (identical? a (j/host-request ready e)))
            (j/resume-host! ready e a 0))
          (let [b (host-request! ready e)] (is (= "B" (name-text ready (first (h/args b))))) (j/resume-host! ready e b 0))
          (let [result (code/finish! ready e)] (is (= "A,B" (names-text ready result))) (j/release! ready e result))
          (let [seed (p/seed! ready e)] (is (= 0 (p/size ready seed))) (j/release! ready e seed)) (j/close! ready e))))))
(deftest original-expansion-forks-while-rehash-body-is-active
  (if-not (:explicit *basis*) (is true "Rehash frame suspension is explicit-driver only")
    (let [{:keys [ctx] :as lab} (context) parent (p/engine lab) keys (mapv #(p/bvar! ctx parent %) (range 96))
          table (reduce #(p/insert! ctx parent %1 %2) (p/seed! ctx parent) keys)
          capacity (.arraySize (p/buckets ctx table)) new-key (p/bvar! ctx parent 96)
          snapshot (p/retain ctx parent table)]
      (is (= 96 (p/size ctx table)))
      (j/start! ctx parent ((p/roles) 1) [table (p/retain ctx parent new-key) 0])
      (expr/until! ctx parent #(= ((p/roles) 2) (some-> (pv parent "active") (pv "label"))))
      (let [{:keys [engine roots]} (j/fork! ctx parent (vec (concat keys [new-key snapshot]))) child engine
            child-keys (subvec roots 0 96) child-new (roots 96) child-snapshot (roots 97)]
        (is (= (mapv pointer/word keys) (mapv pointer/word child-keys)))
        (doseq [[e ks nk old] [[parent keys new-key snapshot] [child child-keys child-new child-snapshot]]]
          (let [out (code/finish! ctx e)]
            (is (= 97 (p/size ctx out))) (is (> (.arraySize (p/buckets ctx out)) capacity))
            (is (= 96 (p/size ctx old))) (is (every? #(= 1 (p/contains! ctx e out %)) (conj ks nk)))
            (j/release! ctx e out))
          (doseq [v (concat ks [nk old])] (j/release! ctx e v)) (j/close! ctx e))))))
(defn u64 [word] (let [v (biginteger word)] (if (neg? word) (.add v (.shiftLeft java.math.BigInteger/ONE 64)) v)))
(defn bucket-index [ctx e word capacity]
  ;; Test-host observation only: use the same original arithmetic primitives on
  ;; an already stamped word to choose a guaranteed collision, not a native hash golden.
  (let [h (p/call ctx e "mixHash" [(u64 word) 11])
        x (p/call ctx e "UInt64.xor" [h (p/call ctx e "UInt64.shiftRight" [h 32])])
        x (p/call ctx e "UInt64.xor" [x (p/call ctx e "UInt64.shiftRight" [x 16])])]
    (int (bit-and (dec capacity) (.longValue ^java.math.BigInteger (biginteger x))))))
(deftest actual-original-bucket-collision-preserves-distinct-key-equality
  (let [{:keys [ctx] :as lab} (context) e (p/engine lab) seed (p/seed! ctx e) capacity (.arraySize (p/buckets ctx seed))
        keys (mapv #(p/bvar! ctx e %) (range (inc capacity)))]
    (doseq [key keys] (is (= 0 (p/contains! ctx e seed key))))
    (let [groups (group-by #(bucket-index ctx e (pointer/word %) capacity) keys)
          [a b] (take 2 (first (filter #(>= (count %) 2) (vals groups))))
          table (p/insert! ctx e (p/insert! ctx e seed a) b)
          at (bucket-index ctx e (pointer/word a) capacity)
          bucket (nth (p/fields ctx (p/buckets ctx table)) at)]
      (is (not (identical? a b))) (is (= 2 (p/size ctx table)))
      (is (not= 0 (last (p/fields ctx bucket))))
      (is (= 1 (p/contains! ctx e table a) (p/contains! ctx e table b)))
      (j/release! ctx e table))
    (doseq [key keys] (j/release! ctx e key)) (j/close! ctx e)))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-pointer-hash-followup-checks)))
