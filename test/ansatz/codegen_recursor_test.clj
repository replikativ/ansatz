(ns ansatz.codegen-recursor-test
  "Kernel/runtime differential guard for recursor representations and minors."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.codegen.storedef :as sd]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [ansatz.malli :as am]
            [ansatz.surface.elaborate :as elab])
  (:import [ansatz.kernel TypeChecker]))

(def ^:private definitions
  '[(ansatz.core/inductive CGEnum [] (red) (green) (blue))
    (ansatz.core/inductive CGPeano [] (z) (s [p CGPeano]))
    (ansatz.core/inductive CGTree [] (leaf) (node [n Nat] [l CGTree] [r CGTree]))
    (ansatz.core/inductive Tw [] (tleaf [n Nat]) (tnode [n Nat] [l Tw] [r Tw]))
    (ansatz.core/inductive Pt [] (mk [x Nat] [y Nat]))
    (ansatz.core/inductive Bt [] (bl) (bn [l Bt] [r Bt]) (bz))
    (ansatz.core/inductive CGBox [α Type] (mk [x α]))
    (ansatz.core/inductive CGRose [] (leaf [n Nat]) (node [kids (List CGRose)]))
    (ansatz.core/defn cg-enum [x :- CGEnum] Nat
      (match x [red 3] [green 5] [blue 7]))
    (ansatz.core/defn cg-peano [x :- CGPeano] Nat
      (match x [z 0] [(s p) (+ 1 (cg-peano p))]))
    (ansatz.core/defn cg-tree [x :- CGTree] Nat
      (match x [leaf 0] [(node n l r) (+ n (+ (cg-tree l) (cg-tree r)))]))
    (ansatz.core/defn twsum [t :- Tw] Nat
      (match t [(tleaf n) n] [(tnode n l r) (+ n (+ (twsum l) (twsum r)))]))
    (ansatz.core/defn tw3 [k :- Nat] Nat (twsum (Tw.tnode k (Tw.tleaf 2) (Tw.tleaf 3))))
    (ansatz.core/defn psum [p :- Pt] Nat (match p [(mk x y) (+ x y)]))
    (ansatz.core/defn p23 [k :- Nat] Nat (psum (Pt.mk k 3)))
    (ansatz.core/defn cg-box [p :- (CGBox Nat)] Nat (match p [(mk x) x]))
    (ansatz.core/defn cg-list [xs :- (List Nat)] Nat
      (match xs [nil 0] [(cons h t) (+ h (cg-list t))]))
    (ansatz.core/defn cg-nat [n :- Nat] Nat
      (match n [zero 0] [(succ p) (+ 1 (cg-nat p))]))
    (ansatz.core/defn cg-prod [p :- (Prod Nat Nat)] Nat
      (match p [(mk x y) (+ x y)]))
    (ansatz.core/defn cg-nested [x :- (Option (List Nat))] Nat
      (match x [none 0] [(some xs) (cg-list xs)]))])

(defn- install! []
  (run! eval definitions)
  (eval (list 'ansatz.core/defn 'obind '[o :- (Option Nat), f :- (=> Nat (Option Nat))]
              '(Option Nat)
              (list (symbol "Option.rec.{1,0}") 'Nat '(fn [_ :- (Option Nat)] (Option Nat))
                    '(Option.none Nat) 'f 'o)))
  (eval '(ansatz.core/defn ob5 [k :- Nat] (Option Nat)
           (obind (Option.some Nat k) (fn [x :- Nat] (Option.some Nat (+ x 1))))))
  (doseq [uses (range 3)]
    (eval (list 'ansatz.core/defn (symbol (str "cg-ih" uses)) '[t :- Bt] 'Nat
                (list (symbol "Bt.rec.{1}") '(fn [_ :- Bt] Nat) 1
                      (list 'fn '[l :- Bt, r :- Bt, il :- Nat, ir :- Nat]
                            (case uses 0 9 1 'il 2 '(+ il il)))
                      0 't))))
  (eval '(ansatz.core/defn cg-step [p :- Nat, ih :- Nat] Nat (+ 1 ih)))
  (eval (list 'ansatz.core/defn 'cg-nat-eta '[n :- Nat] 'Nat
              (list (symbol "Nat.rec.{1}") '(fn [_ :- Nat] Nat) 0 'cg-step 'n)))
  (eval (list 'ansatz.core/defn 'cg-nat-add '[n :- Nat] 'Nat
              (list (symbol "Nat.rec.{1}") '(fn [_ :- Nat] Nat) 0 'Nat.add 'n)))
  (eval (list 'ansatz.core/defn 'cg-nat-double '[n :- Nat] 'Nat
              (list (symbol "Nat.rec.{1}") '(fn [_ :- Nat] Nat) 1
                    '(fn [p :- Nat, ih :- Nat] (+ ih ih)) 'n)))
  (eval (list 'ansatz.core/defn 'cg-list-double '[xs :- (List Nat)] 'Nat
              (list (symbol "List.rec.{1,0}") 'Nat '(fn [_ :- (List Nat)] Nat) 1
                    '(fn [h :- Nat, t :- (List Nat), ih :- Nat] (+ ih ih)) 'xs)))
  (eval '(ansatz.core/defn cg-bstep [l :- Bt, r :- Bt, il :- Nat, ir :- Nat] Nat (+ il il)))
  (eval (list 'ansatz.core/defn 'cg-tag-eta '[t :- Bt] 'Nat
              (list (symbol "Bt.rec.{1}") '(fn [_ :- Bt] Nat) 1 'cg-bstep 0 't)))
  (eval (list 'ansatz.core/defn 'cg-tag-partial '[t :- Bt] 'Nat
              (list (symbol "Bt.rec.{1}") '(fn [_ :- Bt] Nat) 1
                    '(fn [l :- Bt] (cg-bstep l)) 0 't)))
  (eval (list 'ansatz.core/defn 'cg-rose '[r :- CGRose] 'Nat
              (list (symbol "CGRose.rec.{1}")
                    '(fn [_ :- CGRose] Nat) '(fn [_ :- (List CGRose)] Nat)
                    '(fn [n :- Nat] 1) '(fn [kids :- (List CGRose), ih :- Nat] ih)
                    0 '(fn [h :- CGRose, t :- (List CGRose), hh :- Nat, th :- Nat] (+ hh th)) 'r)))
  ;; #118's exact function name/reproducer and kernel theorem.
  (eval (list 'ansatz.core/defn 'dbl '[t :- Bt] 'Nat
              (list (symbol "Bt.rec.{1}") '(fn [_ :- Bt] Nat) 1
                    '(fn [l :- Bt, r :- Bt, il :- Nat, ir :- Nat] (+ il il)) 0 't)))
  (run! eval
        '[(ansatz.core/theorem ob5_kernel [] (= (Option Nat) (ob5 5) (Option.some Nat 6)) (rfl))
          (ansatz.core/theorem tw3_kernel [] (= Nat (tw3 1) 6) (rfl))
          (ansatz.core/theorem p23_kernel [] (= Nat (p23 2) 5) (rfl))
          (ansatz.core/theorem dbl_kernel [] (= Nat (dbl (Bt.bn (Bt.bn Bt.bl Bt.bz) Bt.bz)) 4) (rfl))]))

(defn- differential!
  "Like malli/check-verified!: evaluate a closed application in the kernel and
  compare with the public compiled function. Surface input terms permit custom
  inductives beyond malli's schema codecs; output decoding reuses its WHNF codec."
  [f inputs schema]
  (let [tc (doto (TypeChecker. (a/env)) (.setFuel 200000000))
        red (.getReducer tc)
        whnf #(.whnf red %)
        runtime @(ns-resolve *ns* f)]
    (doseq [input inputs]
      (let [arg (elab/elaborate (a/env) input)
            term (elab/elaborate (a/env) (list f input))
            rt (runtime (eval (cg/ansatz->clj (a/env) arg [])))
            kernel (#'am/decode-val whnf schema term)
            ;; Malli's codec uses nil-punning for Option; base codegen retains
            ;; nil/[value], so compare the decoded payload on both sides.
            decoded-rt (if (= :maybe (when (vector? schema) (first schema)))
                         (when rt (first rt)) rt)]
        (is (= kernel decoded-rt) (str f " " input))))))

(defn- differential-closed!
  ([applications] (differential-closed! applications :int))
  ([applications schema] (differential-closed! applications schema identity))
  ([applications schema kernel-form]
   (let [tc (doto (TypeChecker. (a/env)) (.setFuel 200000000))
         red (.getReducer tc)]
     (doseq [application applications]
       (let [term (elab/elaborate (a/env) application)
             kernel (#'am/decode-val #(.whnf red %) schema
                                     (elab/elaborate (a/env) (kernel-form application)))
             runtime (eval (cg/ansatz->clj (a/env) term []))]
         (is (= kernel runtime) (str application)))))))

(deftest function-valued-definitions-preserve-call-arity
  (let [saved-env @a/ansatz-env
        saved-arity @a/arity-registry
        saved-instances @a/ansatz-instance-index]
    (try
      (binding [*ns* (the-ns 'ansatz.codegen-recursor-test) a/*verbose* false]
        (a/load-init!)
        (run! eval
              '[(ansatz.core/defn round-probe [n :- Nat] (=> Nat Bool)
                  (match n
                    [zero (fn [x :- Nat] true)]
                    [(succ k) (fn [x :- Nat] ((round-probe k) x))]))
                (ansatz.core/defn bad-call-probe [n :- Nat, x :- Nat] Bool
                  ((round-probe n) x))
                (ansatz.core/theorem probe-kernel [] (= (bad-call-probe 2 3) true) (rfl))
                (ansatz.core/defn cg-result-let [n :- Nat, x :- Nat] Bool
                  (let [f (round-probe n)] (f x)))
                (ansatz.core/defn cg-result-flat [n :- Nat, x :- Nat, y :- Nat] Nat
                  (+ n (+ x y)))
                (ansatz.core/defn cg-result-multi [n :- Nat, x :- Nat] (=> Nat Nat)
                  (fn [y :- Nat] (+ n (+ x y))))
                (ansatz.core/defn cg-result-recursive [n :- Nat, x :- Nat] (=> Nat Nat)
                  (match n
                    [zero (fn [y :- Nat] (+ x y))]
                    [(succ k) (fn [y :- Nat] (+ 1 ((cg-result-recursive k x) y)))]))
                (ansatz.core/defn cg-result-eta [n :- Nat] (=> Nat Nat)
                  (fn [x :- Nat] (cg-result-flat n x 3)))
                (ansatz.core/defn cg-result-partial [n :- Nat] (=> Nat Nat)
                  (cg-result-flat n 2))
                (ansatz.core/defn cg-result-nested [n :- Nat] (=> Nat (=> Nat Nat))
                  (fn [x :- Nat] (fn [y :- Nat] (+ n (+ x y)))))
                (ansatz.core/defn cg-result-value [] (=> Nat (=> Nat (=> Nat Nat)))
                  cg-result-flat)
                (ansatz.core/defn cg-result-local [n :- Nat, x :- Nat, y :- Nat] Nat
                  (let [f (cg-result-multi n)] ((f x) y)))
                (ansatz.core/defn ^:partial cg-result-partial-def [n :- Nat] (=> Nat Nat)
                  (fn [x :- Nat] (+ n x)))
                (ansatz.core/foreign cg-result-foreign [n :- Nat] (=> Nat Nat)
                                     (fn [n] (fn [x] (+ n x))))])
        (is (= 1 (:arity (get @a/arity-registry "round-probe"))))
        (is (= 2 (:arity (get @a/arity-registry "cg-result-multi"))))
        (is (= 3 (:arity (get @a/arity-registry "cg-result-flat"))))
        ;; Public runtime calls also exercise the wrappers independently of application lowering.
        (is (true? ((deref (ns-resolve *ns* 'bad-call-probe)) 2 3)))
        (let [multi @(ns-resolve *ns* 'cg-result-multi)]
          (is (= 10 ((multi 2 3) 5)))
          (is (= 10 (((multi 2) 3) 5))))
        (doseq [n (range 5)]
          (differential-closed!
           [(list 'bad-call-probe n 3) (list 'cg-result-let n 3)
            (list (list 'round-probe n) 3)] :boolean)
          (differential-closed!
           [(list 'cg-result-multi n 3 5)
            (list (list 'cg-result-multi n 3) 5)
            (list 'cg-result-eta n 5) (list 'cg-result-partial n 5)
            (list 'cg-result-nested n 3 5) (list 'cg-result-value n 3 5)
            (list 'cg-result-local n 3 5) (list 'cg-result-recursive n 3 5)
            (list 'let '[f cg-result-multi] (list 'f n 3 5))]))
        (doseq [f '[cg-result-partial-def cg-result-foreign]]
          (is (= 1 (:arity (get @a/arity-registry (str f)))))
          (is (= 7 (eval (cg/ansatz->clj (a/env)
                                         (elab/elaborate (a/env) (list f 2 5)) [])))))
        ;; Ordinary functions retain the flat call fast path.
        (is (= '(ansatz.codegen-recursor-test/cg-result-flat 2 3 5)
               (cg/ansatz->clj (a/env)
                               (elab/elaborate (a/env) '(cg-result-flat 2 3 5)) []))))
      (finally
        (reset! a/ansatz-env saved-env)
        (reset! a/arity-registry saved-arity)
        (reset! a/ansatz-instance-index saved-instances)))))

(deftest function-results-agree-across-definition-modes
  (let [saved-env @a/ansatz-env
        saved-arity @a/arity-registry
        saved-instances @a/ansatz-instance-index]
    (try
      (binding [*ns* (the-ns 'ansatz.codegen-recursor-test) a/*verbose* false]
        (a/load-init!)
        (run! eval
              '[(ansatz.core/defn cg-result-oracle [n :- Nat, b :- Nat] (=> Nat Nat)
                  (match n
                    [zero (fn [x :- Nat] (+ b x))]
                    [(succ k) (fn [x :- Nat] (+ 1 ((cg-result-oracle k b) x)))]))
                (ansatz.core/defn cg-result-oracle-value [] (=> Nat Nat)
                  (fn [x :- Nat] (+ x 1)))])
        (doseq [mode [:verified :partial :wf]
                arity (range 3)]
          (let [f (symbol (str "cg-result-" (name mode) "-" arity))
                fn-name (cond-> f (= mode :partial) (with-meta {:partial true}))
                params (case arity 0 [] 1 '[n :- Nat] 2 '[n :- Nat, b :- Nat])
                body (case arity
                       0 '(fn [x :- Nat] (+ x 1))
                       1 '(fn [x :- Nat] (+ n x))
                       2 '(fn [x :- Nat] (+ n (+ b x))))]
            (eval (apply list 'ansatz.core/defn fn-name params '(=> Nat Nat)
                         (concat (when (= mode :wf) [:termination-by (if (zero? arity) 0 'n)])
                                 [body])))
            (is (= arity (:arity (get @a/arity-registry (str f)))))
            (doseq [x (range 5)]
              (let [args (case arity 0 [x] 1 [3 x] 2 [3 2 x])
                    application (apply list f args)
                    ;; Partial declarations are opaque axioms. Their total twins,
                    ;; rather than those axioms, provide the checked kernel oracle.
                    oracle (case arity
                             0 (list 'cg-result-oracle-value x)
                             1 (list 'cg-result-oracle 0 3 x)
                             2 (list 'cg-result-oracle 3 2 x))]
                (differential-closed!
                 [application (list 'let ['f (if (zero? arity) f (apply list f (butlast args)))]
                                    (list 'f (last args)))] :int
                 (if (= mode :partial) (constantly oracle) identity))))))
        ;; Recursive self-calls under returned lambdas, including over-application.
        (doseq [mode [:partial :wf]
                arity (range 3)]
          (let [f (symbol (str "cg-result-rec-" (name mode) "-" arity))
                fn-name (cond-> f (= mode :partial) (with-meta {:partial true}))
                params (case arity 0 [] 1 '[n :- Nat] 2 '[n :- Nat, b :- Nat])
                ;; A nullary WF value has no recursion domain: call a checked
                ;; recursive function from its returned lambda instead.
                body (if (zero? arity)
                       (if (= mode :partial)
                         (list 'fn '[x :- Nat]
                               (list 'if '(<= x 0) 1 (list '+ 1 (list f '(- x 1)))))
                         '(fn [x :- Nat] (cg-result-oracle x 1 0)))
                       (list 'if '(<= n 0)
                             (if (= arity 1) '(fn [x :- Nat] x) '(fn [x :- Nat] (+ b x)))
                             (list 'fn '[x :- Nat]
                                   (list (apply list f (cond-> ['(- n 1)] (= arity 2) (conj 'b)))
                                         '(+ x 1)))))]
            (eval (apply list 'ansatz.core/defn fn-name params '(=> Nat Nat)
                         (concat (when (= mode :wf) [:termination-by (if (zero? arity) 0 'n)])
                                 [body])))
            (when (pos? arity)
              (is (= :surface (:provenance (get @a/arity-registry (str f))))))
            (when (and (= mode :wf) (pos? arity))
              (is (#'a/mentions-const?
                   (.getValue (env/lookup (a/env) (name/from-string (str f))))
                   (name/from-string "WellFounded.Nat.fix"))))
            (doseq [n (range 5)]
              (let [args (case arity 0 [n] 1 [n 4] 2 [n 2 4])
                    application (apply list f args)
                    oracle (case arity
                             0 (list 'cg-result-oracle n 1 0)
                             1 (list 'cg-result-oracle n 0 4)
                             2 (list 'cg-result-oracle n 2 4))]
                (differential-closed! [application] :int
                                      (if (= mode :partial) (constantly oracle) identity))))))
        (eval '(ansatz.core/defn cg-result-wf-fuel [n :- Nat] (=> Nat Nat)
                 :termination-by n
                 (if (<= n 0) (fn [x :- Nat] x)
                     (fn [x :- Nat]
                       (let [y (+ x 1)] (cg-result-wf-fuel (- n 1) y))))))
        ;; A let in the returned lambda takes the existing fuel fallback, whose
        ;; default must itself have the function result type.
        (is (#'a/mentions-const?
             (.getValue (env/lookup (a/env) (name/from-string "cg-result-wf-fuel")))
             (name/from-string "Nat.rec")))
        (differential-closed! '[(cg-result-wf-fuel 0 5) (cg-result-wf-fuel 4 5)])
        (is (thrown-with-msg?
             clojure.lang.ExceptionInfo #"not provably decreasing"
             (a/define-verified-wf 'cg-result-nondecreasing '[n :- Nat] '(=> Nat Nat)
               '(fn [x :- Nat] ((cg-result-nondecreasing n) x)) 'n))))
      (finally
        (reset! a/ansatz-env saved-env)
        (reset! a/arity-registry saved-arity)
        (reset! a/ansatz-instance-index saved-instances)))))

(deftest emitted-parameter-conventions-match-runtime-arities
  (let [saved-env @a/ansatz-env
        saved-arity @a/arity-registry
        saved-instances @a/ansatz-instance-index]
    (try
      (binding [*ns* (the-ns 'ansatz.codegen-recursor-test) a/*verbose* false]
        (a/load-init!)
        (eval '(ansatz.core/defn cc-oracle [n :- Nat] (=> Nat Nat)
                 (match n [zero (fn [x :- Nat] x)]
                        [(succ k) (fn [x :- Nat] (+ 1 ((cc-oracle k) x)))])))
        (doseq [kind [:verified :partial :wf :foreign]
                shape [:explicit :implicit :instance :nullary]
                function? [false true]
                recursive? [false true]
                fallback? [false true]]
          (let [f (symbol (str "cc-" (name kind) "-" (name shape) "-"
                               function? "-" recursive? "-" fallback?))
                params (case shape
                         :explicit '[n :- Nat]
                         :implicit '[S :- Type :implicit, n :- Nat]
                         :instance '[inst :- (Inhabited Nat) :inst, n :- Nat]
                         :nullary [])
                nullary? (= shape :nullary)
                result (if function? '(=> Nat Nat) 'Nat)
                rec-args (case shape :implicit ['S '(- n 1)]
                               :instance ['inst '(- n 1)]
                               ['(- n 1)])
                self (apply list (if (#{:implicit :instance} shape)
                                   (symbol (str "@" f)) f) rec-args)
                body (cond
                       nullary?
                       (if function?
                         (if (and recursive? (= kind :partial))
                           (list 'fn '[x :- Nat]
                                 (list 'if '(<= x 0) 4 (list '+ 1 (list f '(- x 1)))))
                           (if recursive? '(fn [x :- Nat] (cc-oracle 4 x))
                               '(fn [x :- Nat] (+ 4 x))))
                         (if recursive? '(cc-oracle 4 0) 4))
                       recursive?
                       (list 'if '(<= n 0)
                             (if function? '(fn [x :- Nat] x) 0)
                             (if function?
                               (list 'fn '[x :- Nat] (list '+ 1 (list self 'x)))
                               (list '+ 1 self)))
                       function? '(fn [x :- Nat] (+ n x))
                       :else 'n)
                body (if (and (= kind :verified) recursive? (not nullary?))
                       (let [call (apply list (if (#{:implicit :instance} shape)
                                                (symbol (str "@" f)) f)
                                         (case shape :implicit ['S 'k] :instance ['inst 'k] ['k]))]
                         (list 'match 'n
                               ['zero (if function? '(fn [x :- Nat] x) 0)]
                               ['(succ k) (if function?
                                            (list 'fn '[x :- Nat] (list '+ 1 (list call 'x)))
                                            (list '+ 1 call))]))
                       body)
                impl (if nullary?
                       (if function?
                         (if recursive? '(fn self [x] (if (<= x 0) 4 (+ 1 (self (- x 1)))))
                             '(fn [x] (+ 4 x))) 4)
                       (if recursive?
                         (if function?
                           '(fn self [n] (if (<= n 0) (fn [x] x)
                                             (fn [x] (+ 1 ((self (- n 1)) x)))))
                           '(fn self [n] (if (<= n 0) 0 (+ 1 (self (- n 1))))))
                         (if function? '(fn [n] (fn [x] (+ n x))) '(fn [n] n))))
                form (if (= kind :foreign)
                       (list 'ansatz.core/foreign f params result impl)
                       (apply list 'ansatz.core/defn
                              (cond-> f (= kind :partial) (with-meta {:partial true}))
                              params result
                              (concat (when (= kind :wf)
                                        [:termination-by (if nullary? 0 'n)]) [body])))
                install #(eval form)]
            (testing (str [kind shape function? recursive? fallback?])
              (if fallback?
                (with-redefs [sd/emit-direct-recursion (fn [& _] nil)] (install))
                (install))
              (let [cc (get @a/arity-registry (str f))
                    runtime @(ns-resolve *ns* f)
                    arities (when (ifn? runtime)
                              (set (for [m (.getDeclaredMethods (class runtime))
                                         :when (= "invoke" (.getName m))]
                                     (.getParameterCount m))))
                    kernel-prefix (case shape :implicit ['Nat 4]
                                        :instance ['(Inhabited.mk Nat 0) 4]
                                        :explicit [4] :nullary [])
                    application (apply list (if (#{:implicit :instance} shape)
                                              (symbol (str "@" f)) f)
                                       (cond-> kernel-prefix function? (conj 3)))
                    oracle (if function? '(cc-oracle 4 3) '(cc-oracle 4 0))]
                (is (= (:arity cc) (count (:params cc))))
                (is (= nullary? (:value? cc)))
                (if nullary?
                  (is (not (contains? arities 0)))
                  (do
                      ;; Invoke exactly the recorded runtime window, independently
                      ;; of application lowering and its erased kernel prefix.
                    (is (= (if function? 7 4)
                           (let [inputs (mapv #(eval (cg/ansatz->clj (a/env)
                                                                     (elab/elaborate (a/env) %) []))
                                              (drop (:erased cc) kernel-prefix))
                                 v (apply runtime inputs)]
                             (is (= (:arity cc) (count inputs)))
                             (if function? (v 3) v))))))
                (let [kernel-form (if (#{:partial :foreign} kind) oracle application)]
                  (differential-closed! [application] :int (constantly kernel-form))
                  ;; Construct the fully explicit kernel let directly: the surface
                  ;; @ syntax currently resolves constants, not local aliases.
                  (let [term (elab/elaborate (a/env) application)
                        [head args] (e/get-app-fn-args term)
                        tc (TypeChecker. (a/env))
                        alias (e/let' "alias" (.inferType tc head) head
                                      (reduce e/app (e/bvar 0) args))
                        kernel (#'am/decode-val #(.whnf (.getReducer tc) %) :int
                                                (elab/elaborate (a/env) kernel-form))]
                    (is (= kernel (eval (cg/ansatz->clj (a/env) alias []))))))))))

        (run! eval
              '[(ansatz.core/defn original-flat [n :- Nat, x :- Nat] Nat (+ n x))
                (ansatz.core/defn replacement-result [n :- Nat] (=> Nat Nat)
                  (fn [x :- Nat] (+ n x)))
                (ansatz.core/csimp replace-original [n :- Nat, x :- Nat]
                                   (= Nat (original-flat n x) (replacement-result n x)) (rfl))
                (ansatz.core/defn original-result [n :- Nat] (=> Nat Nat)
                  (fn [x :- Nat] (+ n x)))
                (ansatz.core/defn replacement-flat [n :- Nat, x :- Nat] Nat (+ n x))
                (ansatz.core/csimp replace-result [n :- Nat, x :- Nat]
                                   (= Nat (original-result n x) (replacement-flat n x)) (rfl))])
        (doseq [f '[original-flat original-result], n (range 3)]
          (differential-closed!
           [(list f n 3)
            (list 'let ['f f] (list 'f n 3))
            (list 'let ['f f 'g 'f] (list 'g n 3))
            (list 'let ['f (list f n)] '(f 3))]))
        ;; Check both the shorter and longer replacement parameter windows.
        (doseq [[form expected]
                [['(let [f original-flat] (f 2 3))
                  '(let [f ansatz.codegen-recursor-test/replacement-result] ((f 2) 3))]
                 ['(let [f original-result] (f 2 3))
                  '(let [f ansatz.codegen-recursor-test/replacement-flat] (f 2 3))]]]
          (is (= expected (cg/ansatz->clj (a/env) (elab/elaborate (a/env) form) []))))
        ;; A runtime-used instance prefix must be retained by the classic wrapper.
        (eval '(ansatz.core/defn cc-used-instance [inst :- Nat :inst, n :- Nat] Nat (+ inst n)))
        (let [cc (get @a/arity-registry "cc-used-instance")
              runtime @(ns-resolve *ns* 'cc-used-instance)]
          (is (= 0 (:erased cc)))
          (is (= 2 (:arity cc)))
          (is (= 11 (runtime 7 4)))
          (differential-closed! [(list (symbol "@cc-used-instance") 7 4)]))
        ;; The dependent implicit-prefix probe has one runtime parameter plus a
        ;; function-valued result, and must never emit the erased Nat type.
        (eval '(ansatz.core/defn ^:partial poly-result [S :- Type :implicit, n :- S]
                 (=> Nat S) (fn [x :- Nat] n)))
        (with-redefs [sd/emit-direct-recursion (fn [& _] nil)]
          (eval '(ansatz.core/defn ^:partial poly-result-classic [S :- Type :implicit, n :- S]
                   (=> Nat S) (fn [x :- Nat] n))))
        (differential-closed! '[(poly-result 7 3) (poly-result-classic 7 3)
                                (let [f poly-result] (f 7 3))
                                (let [f poly-result-classic] (f 7 3))]
                              :int (constantly 7))
        (is (= 7 (((deref (ns-resolve *ns* 'poly-result)) 7) 3))))
      (finally
        (reset! a/ansatz-env saved-env)
        (reset! a/arity-registry saved-arity)
        (reset! a/ansatz-instance-index saved-instances)))))

(defn- higher-order-differential! []
  ;; Independently exercise higher-order recursors exported by Lean, verifying
  ;; every imported declaration before comparing kernel and runtime results.
  (let [decls (:decls (parser/parse-ndjson-file "test/fixtures/codegen_higher.ndjson"))
        new-decls (filterv #(nil? (env/lookup (a/env) (.name ^ansatz.kernel.ConstantInfo %))) decls)
        result (replay/replay-from-env (a/env) new-decls)]
    (is (zero? (get-in result [:stats :errors])) (str (:results result)))
    (when (pos? (get-in result [:stats :errors]))
      (throw (ex-info "Higher-order fixture failed kernel validation" {:results (:results result)})))
    (reset! a/ansatz-env (:env result)))
  (doseq [[f params rec motive minors tail]
          [['higher-rec '[t :- ReviewHigher] "ReviewHigher.rec.{1}"
            '(fn [_ :- ReviewHigher] Nat)
            '[(fn [n :- Nat] n)
              (fn [f :- (=> Nat ReviewHigher), ih :- (=> Nat Nat)] (ih 0))] '[t]]
           ['cg-higher-leaf '[t :- CGHigherLeaf] "CGHigherLeaf.rec.{1}"
            '(fn [_ :- CGHigherLeaf] Nat)
            '[7 (fn [f :- (=> Nat CGHigherLeaf), ih :- (=> Nat Nat)] (ih 0))] '[t]]
           ['cg-higher-tagged '[t :- CGHigherTagged] "CGHigherTagged.rec.{1}"
            '(fn [_ :- CGHigherTagged] Nat)
            '[(fn [n :- Nat] n)
              (fn [f :- (=> Nat (=> Nat CGHigherTagged)), ih :- (=> Nat (=> Nat Nat))]
                (+ (ih 0 1) (ih 2 3))) 0] '[t]]
           ['cg-higher-single '[t :- CGHigherSingle] "CGHigherSingle.rec.{1}"
            '(fn [_ :- CGHigherSingle] Nat)
            '[(fn [f :- (=> Empty CGHigherSingle), ih :- (=> Empty Nat)] 7)] '[t]]
           ['cg-higher-parameterized '[n :- Nat, t :- (CGHigherIx n)] "CGHigherIx.rec.{1}"
            '(fn [t :- (CGHigherIx n)] Nat)
            '[(fn [payload :- Nat] payload)
              (fn [f :- (=> Nat (CGHigherIx n)), ih :- (=> Nat Nat)] (ih 0))] '[t]]
           ['cg-higher-indexed '[n :- Nat, t :- (CGHigherIndexed n)] "CGHigherIndexed.rec.{1}"
            '(fn [n :- Nat, t :- (CGHigherIndexed n)] Nat)
            '[(fn [k :- Nat, payload :- Nat] payload)
              (fn [k :- Nat, f :- (=> Nat (CGHigherIndexed k)), ih :- (=> Nat Nat)] (ih 0))] '[n t]]]]
    (let [prefix (if (= f 'cg-higher-parameterized) ['n motive] [motive])]
      (eval (list 'ansatz.core/defn f params 'Nat
                  (apply list (symbol (str "@" rec)) (concat prefix minors tail))))))
  (eval '(ansatz.core/theorem higher-rec-kernel []
                              (= Nat (higher-rec (ReviewHigher.node (fn [_ :- Nat] (ReviewHigher.leaf 7)))) 7)
                              (rfl)))
  (is (= 7 ((deref (ns-resolve *ns* 'higher-rec)) [0 7])))
  (is (= 7 ((deref (ns-resolve *ns* 'higher-rec)) [1 (fn [_] [0 7])])))
  (doseq [n (range 9)]
    (let [higher-tree (nth (iterate #(list 'ReviewHigher.node (list 'fn '[_ :- Nat] %))
                                    (list 'ReviewHigher.leaf n)) 4)
          leaf-tree (nth (iterate #(list 'CGHigherLeaf.node (list 'fn '[_ :- Nat] %))
                                  'CGHigherLeaf.leaf) 4)
          tagged-tree (list 'CGHigherTagged.node
                            (list 'fn '[x :- Nat] (list 'fn '[y :- Nat]
                                                        (list 'CGHigherTagged.leaf (list '+ n '(+ x y))))))
          ix-tree (nth (iterate #(list 'CGHigherIx.node n (list 'fn '[_ :- Nat] %))
                                (list 'CGHigherIx.leaf n (+ n 3))) 4)]
      (differential-closed!
       [(list 'higher-rec (list 'ReviewHigher.leaf n))
        (list 'higher-rec (list 'ReviewHigher.node
                                (list 'fn '[x :- Nat] (list 'ReviewHigher.leaf (list '+ n 'x)))))
        (list 'higher-rec higher-tree)
        (list 'cg-higher-leaf 'CGHigherLeaf.leaf)
        (list 'cg-higher-leaf leaf-tree)
        (list 'cg-higher-tagged (list 'CGHigherTagged.leaf n))
        (list 'cg-higher-tagged tagged-tree)
        '(cg-higher-tagged CGHigherTagged.end)
        (list 'cg-higher-parameterized n (list 'CGHigherIx.leaf n (+ n 3)))
        (list 'cg-higher-parameterized n ix-tree)
        (list 'cg-higher-indexed n (list 'CGHigherIndexed.leaf n (+ n 3)))
        (list 'cg-higher-indexed (+ n 4)
              (second (nth (iterate (fn [[k tree]]
                                      [(inc k) (list 'CGHigherIndexed.node k (list 'fn '[_ :- Nat] tree))])
                                    [n (list 'CGHigherIndexed.leaf n (+ n 3))]) 4)))])))
  (differential-closed!
   [(list 'cg-higher-single
          (list 'CGHigherSingle.mk
                (list 'fn '[e :- Empty]
                      (list (symbol "@Empty.rec.{1}") '(fn [_ :- Empty] CGHigherSingle) 'e))))])
  ;; IH lambdas are lazy: neither constructing nor sharing one may apply f.
  (eval (list 'ansatz.core/defn 'cg-higher-lazy '[t :- ReviewHigher] 'Nat
              (list (symbol "@ReviewHigher.rec.{1}") '(fn [_ :- ReviewHigher] Nat)
                    '(fn [n :- Nat] n)
                    '(fn [f :- (=> Nat ReviewHigher), ih :- (=> Nat Nat)]
                       (if true 7 (+ (ih 0) (ih 1)))) 't)))
  (is (= 7 ((deref (ns-resolve *ns* 'cg-higher-lazy))
            [1 (fn [_] (throw (ex-info "forced unused functional field" {})))])))
  (is (= 7 ((deref (ns-resolve *ns* 'cg-higher-single))
            [(fn [_] (throw (ex-info "forced Empty-domain field" {})))]))))

(defn- registered-enum-differential! []
  (doseq [members [[:only] [:a :b] [:a :b :c]]]
    (let [ty (am/ensure-enum! members)
          tn (name/->string (e/const-name ty))
          ts (symbol tn)
          f (symbol (str "cg-registered-enum-" (count members)))
          minors (mapv #(+ 11 (* 11 %)) (range (count members)))
          rec (symbol (str tn ".rec.{1}"))]
      (eval (list 'ansatz.core/defn f ['x :- ts] 'Nat
                  (apply list rec (list 'fn ['x :- ts] 'Nat) (concat minors ['x]))))
      ;; Construction and elimination run under the SAME installed registry.
      (differential-closed! (mapv #(list f (symbol (str tn ".c" %))) (range (count members))))
      (let [probe (symbol (str "cg-enum-construct-eliminate-" (count members)))]
        (eval (list 'ansatz.core/defn probe '[dummy :- Nat] 'Nat
                    (apply list rec (list 'fn ['x :- ts] 'Nat)
                           (concat minors [(symbol (str tn ".c0"))]))))
        (differential! probe (range 4) :int)
        (eval (list 'ansatz.core/theorem (symbol (str probe "-kernel")) []
                    (list '= 'Nat (list probe 0) 11) '(rfl)))))))

(defn- parameterized-enum-differential! []
  (eval '(ansatz.core/inductive CGParamEnum [α Type] (left) (right)))
  (doseq [ctor ["left" "right"]]
    (swap! a/codegen-registry assoc (str "CGParamEnum." ctor)
           (fn [_ expr _]
             (let [[_ args] (e/get-app-fn-args expr)]
               (keyword (str ctor (if (and (seq args) (e/const? (first args))
                                           (= "Nat" (name/->string (e/const-name (first args)))))
                                    "-nat" "-other")))))))
  (eval (list 'ansatz.core/defn 'cg-param-enum '[x :- (CGParamEnum Nat)] 'Nat
              (list (symbol "CGParamEnum.rec.{1}") 'Nat
                    '(fn [x :- (CGParamEnum Nat)] Nat) 11 22 'x)))
  (differential-closed! '[(cg-param-enum (CGParamEnum.left Nat))
                          (cg-param-enum (CGParamEnum.right Nat))]))

(defn- indexed-differential! []
  (run! eval
        '[(ansatz.core/inductive IndexedPair [] :indices [n Nat]
                                 (mk [k Nat] [payload Nat] :where [k]))
          (ansatz.core/inductive CGIxList [] :indices [n Nat]
                                 (nil :where [0])
                                 (cons [k Nat] [h Nat] [t (CGIxList k)] :where [(Nat.succ k)]))
          (ansatz.core/inductive CGIxTagged [] :indices [n Nat]
                                 (leaf [k Nat] [payload Nat] :where [k])
                                 (node [k Nat] [l (CGIxTagged k)] [r (CGIxTagged k)] :where [k])
                                 (end [k Nat] :where [k]))
          (ansatz.core/inductive CGIxPair [α Type] :indices [n Nat, m Nat]
                                 (mk [k Nat] [j Nat] [payload α] :where [k j]))
          (ansatz.core/inductive CGIxEnum [] :indices [n Nat]
                                 (a :where [0]) (b :where [1]) (c :where [2]))])
  (doseq [[f params rec motive minors tail]
          [['indexed-get '[n :- Nat, p :- (IndexedPair n)] "IndexedPair.rec.{1}"
            '(fn [n :- Nat, p :- (IndexedPair n)] Nat)
            '[(fn [k :- Nat, payload :- Nat] payload)] '[n p]]
           ['cg-ix-list '[n :- Nat, p :- (CGIxList n)] "CGIxList.rec.{1}"
            '(fn [n :- Nat, p :- (CGIxList n)] Nat)
            '[0 (fn [k :- Nat, h :- Nat, t :- (CGIxList k), ih :- Nat] (+ h ih))] '[n p]]
           ['cg-ix-tagged '[n :- Nat, p :- (CGIxTagged n)] "CGIxTagged.rec.{1}"
            '(fn [n :- Nat, p :- (CGIxTagged n)] Nat)
            '[(fn [k :- Nat, payload :- Nat] payload)
              (fn [k :- Nat, l :- (CGIxTagged k), r :- (CGIxTagged k), il :- Nat, ir :- Nat] (+ il ir))
              (fn [k :- Nat] 0)] '[n p]]
           ['cg-ix-pair '[n :- Nat, m :- Nat, p :- (CGIxPair Nat n m)] "CGIxPair.rec.{1}"
            '(fn [n :- Nat, m :- Nat, p :- (CGIxPair Nat n m)] Nat)
            '[(fn [k :- Nat, j :- Nat, payload :- Nat] payload)] '[n m p]]
           ['cg-ix-enum '[n :- Nat, p :- (CGIxEnum n)] "CGIxEnum.rec.{1}"
            '(fn [n :- Nat, p :- (CGIxEnum n)] Nat) '[11 22 33] '[n p]]]]
    (let [prefix (if (= f 'cg-ix-pair) ['Nat motive] [motive])]
      (eval (list 'ansatz.core/defn f params 'Nat
                  (apply list (symbol rec) (concat prefix minors tail))))))
  (eval (list 'ansatz.core/defn 'indexed-get-extra
              '[n :- Nat, p :- (IndexedPair n), x :- Nat] 'Nat
              (list (symbol "@IndexedPair.rec.{1}")
                    '(fn [n :- Nat, p :- (IndexedPair n)] (=> Nat Nat))
                    '(fn [k :- Nat, payload :- Nat] (fn [x :- Nat] (+ payload x))) 'n 'p 'x)))
  (eval '(ansatz.core/theorem indexed-get-kernel []
                              (= Nat (indexed-get 3 (IndexedPair.mk 3 17)) 17) (rfl)))
  (is (= 17 ((deref (ns-resolve *ns* 'indexed-get)) 3 [3 17])))
  (doseq [n (range 9)]
    (let [partial-form (list (symbol "@IndexedPair.rec.{1}")
                             '(fn [n :- Nat, p :- (IndexedPair n)] Nat)
                             '(fn [k :- Nat, payload :- Nat] payload) n)
          partial-term (elab/elaborate (a/env) partial-form)
          partial-runtime (eval (cg/ansatz->clj (a/env) partial-term []))
          xs (reduce (fn [tail k] (list 'CGIxList.cons k (+ 2 k) tail))
                     'CGIxList.nil (range n))
          tree (nth (iterate #(list 'CGIxTagged.node n % (list 'CGIxTagged.leaf n 1))
                             (list 'CGIxTagged.leaf n 3)) n)]
      (let [tc (TypeChecker. (a/env))
            input (elab/elaborate (a/env) (list 'IndexedPair.mk n (+ n 17)))
            kernel (#'am/decode-val #(.whnf (.getReducer tc) %) :int (e/app partial-term input))]
        (is (= kernel (partial-runtime [n (+ n 17)]))))
      (differential-closed!
       [(list 'indexed-get n (list 'IndexedPair.mk n (+ 17 n)))
        (list 'indexed-get-extra n (list 'IndexedPair.mk n (+ 17 n)) 5)
        (list 'cg-ix-list n xs)
        (list 'cg-ix-tagged n tree)
        (list 'cg-ix-tagged n (list 'CGIxTagged.end n))
        (list 'cg-ix-pair n (+ n 1) (list 'CGIxPair.mk 'Nat n (+ n 1) (+ n 7)))])))
  (differential-closed! '[(cg-ix-enum 0 CGIxEnum.a) (cg-ix-enum 1 CGIxEnum.b)
                          (cg-ix-enum 2 CGIxEnum.c)]))

(defn- definition-error-kind [form]
  (try (eval form) nil
       (catch clojure.lang.Compiler$CompilerException ex
         (let [cause (.getCause ex)]
           (if (and (instance? clojure.lang.ExceptionInfo cause)
                    (= :codegen-error (:kind (ex-data cause))))
             :codegen-error
             (throw ex))))
       (catch clojure.lang.ExceptionInfo ex
         (if (= :codegen-error (:kind (ex-data ex))) :codegen-error (throw ex)))))

(deftest inductive-differential-and-issue-regressions
  (let [saved-env @a/ansatz-env
        saved-arity @a/arity-registry
        saved-codegen @a/codegen-registry
        saved-structures @a/structure-registry
        saved-instances @a/ansatz-instance-index]
    (try
      (binding [*ns* (the-ns 'ansatz.codegen-recursor-test) a/*verbose* false]
        (a/load-init!)
        (install!)
        (registered-enum-differential!)
        (parameterized-enum-differential!)
        (indexed-differential!)
        (higher-order-differential!)
        ;; Missing indices leave a valid dependent function in the kernel, but
        ;; this lowering supports partial application only when the major is missing.
        (is (= :codegen-error
               (definition-error-kind
                 (list 'ansatz.core/defn 'cg-missing-index '[dummy :- Nat]
                       '(forall [n Nat, p (IndexedPair n)] Nat)
                       (list (symbol "@IndexedPair.rec.{1}")
                             '(fn [n :- Nat, p :- (IndexedPair n)] Nat)
                             '(fn [k :- Nat, payload :- Nat] payload))))))
        (differential! 'cg-enum '[CGEnum.red CGEnum.green CGEnum.blue] :int)
        (doseq [n (range 9)]
          (let [peano (nth (iterate #(list 'CGPeano.s %) 'CGPeano.z) n)
                spine (nth (iterate #(list 'Bt.bn % 'Bt.bz) 'Bt.bl) n)
                roses (reduce #(list 'List.cons 'CGRose (list 'CGRose.leaf %2) %1)
                              '(List.nil CGRose) (range n))
                xs (reduce #(list 'List.cons 'Nat %2 %1) '(List.nil Nat) (range n))]
            (doseq [[f inputs schema]
                    [['cg-peano [peano] :int]
                     ['cg-rose [(list 'CGRose.node roses) (list 'CGRose.node (list 'List.cons 'CGRose (list 'CGRose.node roses) '(List.nil CGRose)))] :int]
                     ['cg-nat [n] :int]
                     ['cg-nat-eta [n] :int]
                     ['cg-nat-add [n] :int]
                     ['cg-nat-double [n] :int]
                     ['cg-list-double [xs] :int]
                     ['cg-list [xs] :int]
                     ['cg-tree [(list 'CGTree.node n 'CGTree.leaf
                                      (list 'CGTree.node 2 'CGTree.leaf 'CGTree.leaf))] :int]
                     ['twsum [(list 'Tw.tnode n (list 'Tw.tleaf 2) (list 'Tw.tleaf 3))] :int]
                     ['tw3 [n] :int]
                     ['psum [(list 'Pt.mk n 3)] :int]
                     ['p23 [n] :int]
                     ['cg-box [(list 'CGBox.mk 'Nat n)] :int]
                     ['cg-prod [(list 'Prod.mk 'Nat 'Nat n 3)] :int]
                     ['cg-nested [(list 'Option.some '(List Nat) xs) '(Option.none (List Nat))] :int]
                     ['ob5 [n] [:maybe :int]]
                     ['cg-ih0 [spine] :int]
                     ['cg-ih1 [spine] :int]
                     ['cg-ih2 [spine] :int]
                     ['dbl [spine] :int]
                     ['cg-tag-eta [spine] :int]
                     ['cg-tag-partial [spine] :int]]]
              (differential! f inputs schema))))
        (testing "#113: eta-reduced minor applies in the outer context"
          (is (= [6] ((deref (ns-resolve *ns* 'ob5)) 5)))
          (is (= [6] ((deref (ns-resolve *ns* 'obind)) [5] #(vector (inc %))))))
        (testing "#118: duplicated IH is shared at depth 28"
          (let [spine (nth (iterate #(vector 1 % [2]) [0]) 28)
                start (System/nanoTime)]
            (is (= 268435456 ((deref (ns-resolve *ns* 'dbl)) spine)))
            (is (< (/ (- (System/nanoTime) start) 1e9) 1.0)))
          (doseq [[f input] [['cg-nat-double 28] ['cg-list-double (repeat 28 0)]]]
            (let [start (System/nanoTime)]
              (is (= 268435456 ((deref (ns-resolve *ns* f)) input)))
              (is (< (/ (- (System/nanoTime) start) 1e9) 1.0)))))
        (testing "unused IHs remain lazy, including repeated uses in an unchosen branch"
          ;; An invalid child exposes accidental eager recursion without timing assertions.
          (eval (list 'ansatz.core/defn 'cg-lazy '[t :- Bt] 'Nat
                      (list (symbol "Bt.rec.{1}") '(fn [_ :- Bt] Nat) 1
                            '(fn [l :- Bt, r :- Bt, il :- Nat, ir :- Nat]
                               (if true 7 (+ il il))) 0 't)))
          (is (= 7 ((deref (ns-resolve *ns* 'cg-lazy)) [1 :unreachable :unreachable]))))
        (testing "nested IH sharing also retains branch laziness"
          (eval (list 'ansatz.core/defn 'cg-rose-lazy '[r :- CGRose] 'Nat
                      (list (symbol "CGRose.rec.{1}")
                            '(fn [_ :- CGRose] Nat) '(fn [_ :- (List CGRose)] Nat)
                            '(fn [n :- Nat] 1)
                            '(fn [kids :- (List CGRose), ih :- Nat] (if true 7 (+ ih ih)))
                            0 '(fn [h :- CGRose, t :- (List CGRose), hh :- Nat, th :- Nat] (+ hh th)) 'r)))
          (is (= 7 ((deref (ns-resolve *ns* 'cg-rose-lazy)) [1 :unreachable]))))
        (testing "#74: const registry overrides nullary constructor representation"
          (let [t (am/ensure-enum! [:a :b :c])
                type-name (name/->string (e/const-name t))]
            (is (= [:a :b :c]
                   (mapv #(cg/ansatz->clj (a/env)
                                          (e/const' (name/from-string (str type-name ".c" %)) []) [])
                         (range 3)))))
          (let [original @a/codegen-registry]
            (try
              (swap! a/codegen-registry assoc "Pt.mk" (fn [_ _ _] :opaque-pair))
              (is (= :codegen-error
                     (definition-error-kind
                       '(ansatz.core/defn cg-unsupported-pair [p :- Pt] Nat
                          (match p [(mk x y) (+ x y)])))))
              (swap! a/codegen-registry assoc "IndexedPair.mk" (fn [_ _ _] :opaque-indexed))
              (is (= :codegen-error
                     (definition-error-kind
                       (list 'ansatz.core/defn 'cg-unsupported-indexed
                             '[n :- Nat, p :- (IndexedPair n)] 'Nat
                             (list (symbol "@IndexedPair.rec.{1}")
                                   '(fn [n :- Nat, p :- (IndexedPair n)] Nat)
                                   '(fn [k :- Nat, payload :- Nat] payload) 'n 'p)))))
              (swap! a/codegen-registry assoc "Bt.bl" (fn [_ _ _] :opaque-leaf))
              (is (= :codegen-error
                     (definition-error-kind
                       '(ansatz.core/defn cg-unsupported-leaf [p :- Bt] Nat
                          (match p [bl 1] [(bn l r) 2] [bz 0])))))
              (swap! a/codegen-registry assoc "CGEnum.red" (fn [_ _ _] :same)
                     "CGEnum.green" (fn [_ _ _] :same))
              (is (= :codegen-error
                     (definition-error-kind
                       '(ansatz.core/defn cg-ambiguous-enum [x :- CGEnum] Nat
                          (match x [red 1] [green 2] [blue 3])))))
              (finally (reset! a/codegen-registry original))))
          (doseq [[ctor v] [["CGEnum.red" :red] ["CGEnum.green" false] ["CGEnum.blue" nil]]]
            (swap! a/codegen-registry assoc ctor (fn [_ _ _] v))
            (is (= v (cg/ansatz->clj (a/env) (e/const' (name/from-string ctor) []) []))))
          (eval '(ansatz.core/defn cg-mixed-enum [x :- CGEnum] Nat
                   (match x [red 1] [green 2] [blue 3])))
          (differential-closed! '[(cg-mixed-enum CGEnum.red) (cg-mixed-enum CGEnum.green)
                                  (cg-mixed-enum CGEnum.blue)])))
      (finally
        (reset! a/ansatz-env saved-env)
        (reset! a/arity-registry saved-arity)
        (reset! a/codegen-registry saved-codegen)
        (reset! a/structure-registry saved-structures)
        (reset! a/ansatz-instance-index saved-instances)))))

(deftest unsupported-recursor-fails-during-codegen
  (let [nm (name/from-string "Unsupported.rec")
        en (env/add-constant (env/empty-env)
                             (env/mk-recursor nm [] (e/sort' level/zero)
                                              :num-motives 2 :num-minors 0))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"unsupported recursor shape"
                          (cg/ansatz->clj en (e/app (e/const' nm []) (e/lit-nat (biginteger 0))) [])))))
