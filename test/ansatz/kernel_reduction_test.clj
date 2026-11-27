(ns ansatz.kernel-reduction-test
  "Reduction, inference and definitional equality against Lean v4.36.0's type_checker.cpp.
   The Lean outcomes are observed with `Lean.Kernel.whnf` / `Lean.Kernel.isDefEq` in
   test/lean-parity/kernel/Reduction.lean."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as te]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red]
            [ansatz.kernel.tc :as ktc])
  (:import [ansatz.kernel ConstantInfo Env Expr KernelAbort LeanExprKey Name Reducer TypeChecker]))

(def ^:private fuel 20000000)
(defn- n [s] (name/from-string s))
(defn- c ([s] (e/const' (n s) [])) ([s ls] (e/const' (n s) ls)))
(def ^:private l0 lvl/zero)
(def ^:private l1 (lvl/succ lvl/zero))
(def ^:private type0 (e/sort' l1))
(defn- pi [nm dom body] (e/forall' nm dom body :default))
(defn- lam [nm dom body] (e/lam nm dom body :default))
(defn- lit [k] (e/lit-nat (biginteger k)))

(def ^:private base (delay @te/bundled-init-env))

(defn- tc
  (^TypeChecker [env] (tc env fuel))
  (^TypeChecker [env f] (doto (TypeChecker. ^Env env) (.setFuel (long f)))))
(defn- whnf [env ex] (.whnf (.getReducer (tc env)) ex))
(defn- defeq? [env a b] (.isDefEq (tc env) a b))
(defn- kernel-error
  "The message of the kernel error `f` raises — a RuntimeException, never a JVM error such as
   StackOverflowError — or nil when `f` returns."
  [f]
  (try (f) nil (catch RuntimeException ex (str (.getMessage ex)))))
(defn- same? [^Expr a ^Expr b] (.equals (LeanExprKey. a) (LeanExprKey. b)))

(def ^:private st-env
  (delay
    (let [env (env/add-inductive @base (env/mk-inductive-decl [] 0 false [["KS" type0 [["KS.mk" (pi "x" (c "Nat") (c "KS"))]]]]) fuel)
          env (env/add-inductive env (env/mk-inductive-decl [] 0 false [["KT" type0 [["KT.mk" (pi "x" (c "Nat") (c "KT"))]]]]) fuel)]
      (env/check-constant env (env/mk-axiom (n "kax") [] (c "KS")) fuel))))

(deftest projections-are-owner-checked
  (testing "reduce_proj_core: a constructor of another structure is not projected"
    (let [term (e/proj (n "KS") 0 (e/app (c "KT.mk") (lit 1)))]
      (is (= (str term) (str (whnf @st-env term))))))
  (testing "projection congruence requires the same structure"
    (is (false? (defeq? @st-env (e/proj (n "KS") 0 (c "kax")) (e/proj (n "KT") 0 (c "kax")))))))

(deftest constructor-heads-are-looked-up-with-env-get
  ;; reduce_proj_core and is_non_rec_structure use env.get: an unknown name is an error (Lean)
  (is (re-find #"Unknown constant: KMissing"
               (str (kernel-error #(whnf @st-env (e/proj (n "KS") 0 (c "KMissing"))))))))

(deftest nat-primitives-match-complete-constants-and-limits
  (testing "Nat.add.{0} is not the primitive Nat.add"
    (let [term (e/app* (c "Nat.add" [l0]) (lit 2) (lit 3))]
      (is (= (str term) (str (whnf @base term))))))
  (testing "Nat.pow checks its 32-bit exponent before the base"
    (is (re-find #"does not fit in a 32-bit unsigned integer"
                 (str (kernel-error #(whnf @base (e/app* (c "Nat.pow") (lit 1) (lit 4294967296))))))))
  (testing "Nat.shiftRight has no count limit"
    (is (= (str (lit 0)) (str (whnf @base (e/app* (c "Nat.shiftRight") (lit 1) (lit 4294967296)))))))
  (testing "Nat.zero.{0} is not Nat.zero: proof irrelevance infers it and rejects the universe arity"
    (is (re-find #"Universe level mismatch for Nat.zero"
                 (str (kernel-error #(defeq? @base (c "Nat.zero" [l0]) (lit 0))))))))

(deftest nat-results-the-jvm-cannot-represent-are-refused
  ;; under a configured limit that admits them (600 MiB / unlimited) Lean computes these; a
  ;; BigInteger cannot hold them, and narrowing the count made `1 <<< 4294967295` zero. The
  ;; refusal comes before any allocation.
  (let [mib600 (* 600 1024 1024)]
    (is (thrown-with-msg? RuntimeException #"cannot be represented"
                          (Reducer/natBinop Name/NAT_SHIFT_LEFT BigInteger/ONE (biginteger 4294967295) mib600)))
    (is (thrown-with-msg? RuntimeException #"cannot be represented"
                          (Reducer/natBinop Name/NAT_POW (biginteger 2) (biginteger 4294967295) -1)))
    (testing "within the default limit the same count is Lean's size refusal"
      (is (thrown-with-msg? RuntimeException #"exceeds the maximum"
                            (Reducer/natBinop Name/NAT_SHIFT_LEFT BigInteger/ONE (biginteger 4294967295)
                                              Reducer/NAT_MAX_BYTES_DEFAULT))))))

(deftest nat-size-setting-reads-as-strtoull
  (let [d 99
        rd #(Reducer/readNatSizeSetting % d)]
    (is (= 7 (rd " 7")) "leading whitespace")
    (is (= 7 (rd "\t+7")))
    (is (= -1 (rd "-1")) "a minus negates modulo 2^64")
    (is (= -1 (rd "99999999999999999999999")) "out of range reads as ULLONG_MAX")
    (is (= -1 (rd "18446744073709551615")))
    (is (= 0 (rd "-0")))
    (doseq [s ["" " " "-" "7 " "7x" "abc" "0x10"]]
      (is (= d (rd s)) (pr-str s))))
  (testing "byte sizes: a value below 2^63 is one word, larger ones whole 64-bit limbs"
    (is (= 8 (Reducer/natBytes BigInteger/ZERO)))
    (is (= 8 (Reducer/natBytes (.subtract (.shiftLeft BigInteger/ONE 63) BigInteger/ONE))))
    (is (= 8 (Reducer/natBytes (.shiftLeft BigInteger/ONE 63))))
    (is (= 16 (Reducer/natBytes (.shiftLeft BigInteger/ONE 64)))))
  (testing "with a 7-byte limit even 0 (one 8-byte word) is refused"
    (is (thrown-with-msg? RuntimeException #"exceeds the maximum"
                          (Reducer/natBinop Name/NAT_ADD BigInteger/ZERO BigInteger/ZERO 7)))
    (is (some? (Reducer/natBinop Name/NAT_ADD BigInteger/ZERO BigInteger/ZERO 8)))))

(deftest int-reduces-through-its-definitions
  (testing "Int.neg on a bare Nat literal unfolds to Int.rec and sticks there (Lean prints
   `Int.rec (fun a => …) (fun a => …) 3`)"
    (let [r (whnf @base (e/app (c "Int.neg") (lit 3)))
          [head args] (e/get-app-fn-args r)]
      (is (= (n "Int.rec") (e/const-name head)))
      (is (= 4 (count args)))
      (is (= (str (lit 3)) (str (last args))))))
  (testing "Int arithmetic still computes"
    (let [i (fn [k] (e/app (c "Int.ofNat") (lit k)))]
      (is (defeq? @base (e/app* (c "Int.add") (i 2) (i 3)) (i 5)))
      (is (defeq? @base (e/app* (c "Int.mul") (e/app (c "Int.negSucc") (lit 6)) (i 3))
            (e/app (c "Int.negSucc") (lit 20)))))))

(deftest kernel-errors-propagate-out-of-proof-irrelevance
  ;; equivalent, structurally different universes: no quick answer, so is_def_eq_proof_irrel
  ;; infers the unknown constant and the error escapes
  (let [u (lvl/param (n "u")) v (lvl/param (n "v"))]
    (is (re-find #"Unknown constant: KUnknown"
                 (str (kernel-error #(defeq? @base (c "KUnknown" [(lvl/level-max (lvl/succ u) (lvl/succ v))])
                                       (c "KUnknown" [(lvl/level-max (lvl/succ v) (lvl/succ u))]))))))))

;; ------------------------------------------------------------------ lazy delta: bounds

(def ^:private alias-env
  (delay
    (reduce (fn [env i]
              (env/check-constant env (env/mk-def (n (str "kalias" i)) [] (c "Nat")
                                                  (if (zero? i) (c "Nat.zero") (c (str "kalias" (dec i))))
                                                  :hints {:regular (inc i)})
                                  fuel))
            @base (range 10002))))

(def ^:private proj-alias-env
  (delay
    (reduce (fn [env i]
              (env/check-constant env (env/mk-def (n (str "kpa" i)) [] (c "KS")
                                                  (if (zero? i) (e/app (c "KS.mk") (lit 1)) (c (str "kpa" (dec i))))
                                                  :hints {:regular (inc i)})
                                  fuel))
            @st-env (range 10002))))

(def ^:private cyclic-env
  ;; unchecked cyclic aliases: lazy delta unfolds them forever
  (delay
    (-> @st-env
        (env/add-constant (env/mk-def (n "kcyc") [] (c "Nat") (c "kcyc") :hints {:regular 1}))
        (env/add-constant (env/mk-def (n "kcycS") [] (c "KS") (c "kcycS") :hints {:regular 1})))))

(defn- proj0 [x] (e/proj (n "KS") 0 x))

(deftest lazy-delta-has-no-step-cutoff
  (testing "lazy_delta_reduction: a 10,001-alias chain"
    (is (defeq? @alias-env (c "kalias10001") (c "Nat.zero"))))
  (testing "lazy_delta_proj_reduction: a 10,001-alias chain under a projection"
    (is (defeq? @proj-alias-env (proj0 (c "kpa10001")) (proj0 (c "kpa0"))))))

(deftest lazy-delta-unfoldings-are-charged
  (testing "every lazy unfolding costs fuel"
    (is (re-find #"fuel exhausted"
                 (str (kernel-error #(.isDefEq (tc @alias-env 1000) (c "kalias10001") (c "Nat.zero"))))))
    (is (re-find #"fuel exhausted"
                 (str (kernel-error #(.isDefEq (tc @proj-alias-env 1000) (proj0 (c "kpa10001")) (proj0 (c "kpa0"))))))))
  (testing "a cyclic alias exhausts the fuel in both loops"
    (is (re-find #"fuel exhausted" (str (kernel-error #(defeq? @cyclic-env (c "kcyc") (c "Nat.zero"))))))
    (is (re-find #"fuel exhausted"
                 (str (kernel-error #(defeq? @cyclic-env (proj0 (c "kcycS")) (proj0 (c "kax")))))))))

(defn- interrupted-outcome
  "Run `f` on a thread, interrupt it after 300 ms; what it ended with."
  [f]
  (let [res (promise)
        t (Thread. ^Runnable (fn [] (deliver res (try (f) :returned (catch Throwable ex ex)))))]
    (.start t)
    (Thread/sleep 300)
    (.interrupt t)
    (.join t 20000)
    (deref res 1000 :still-running)))

(deftest lazy-delta-polls-for-interruption
  ;; unlimited fuel (0): only the interruption ends the cyclic unfolding
  (doseq [[label a b] [["lazy_delta_reduction" (c "kcyc") (c "Nat.zero")]
                       ["lazy_delta_proj_reduction" (proj0 (c "kcycS")) (proj0 (c "kax"))]]]
    (let [r (interrupted-outcome #(.isDefEq (tc @cyclic-env 0) a b))]
      (is (instance? KernelAbort r) label)
      (is (re-find #"interrupted" (str (when (instance? Throwable r) (.getMessage ^Throwable r)))) label))))

(deftest succ-chains-compare-without-stack
  ;; is_def_eq_offset strips one succ per pass; the passes run in a loop, not as nested calls
  (let [k 200000
        chain (reduce (fn [x _] (e/app (c "Nat.succ") x)) (lit 0) (range k))]
    (is (defeq? @base chain (lit k)))
    (is (false? (defeq? @base chain (lit (inc k)))))))

;; ------------------------------------------------------------------ the nested-pair regression

(def ^:private nested-env
  ;; ka opaque; kb := ka; kh : ka = kb
  (delay
    (let [env (env/check-constant @base (env/mk-axiom (n "ka") [] (c "Nat")) fuel)
          env (env/check-constant env (env/mk-def (n "kb") [] (c "Nat") (c "ka") :hints {:regular 1}) fuel)]
      (env/check-constant env (env/mk-axiom (n "kh") [] (e/app* (c "Eq" [l1]) (c "Nat") (c "ka") (c "kb"))) fuel))))

(defn- eq-rec-levels
  "Eq.rec.{u, u_1}: u is the motive's universe, u_1 the carrier's."
  [env motive-level alpha-level]
  (let [^ConstantInfo ci (env/lookup env (n "Eq.rec"))]
    (assert (= ["u" "u_1"] (mapv str (.levelParams ci))))
    [motive-level alpha-level]))

(deftest a-nested-comparison-keeps-the-outer-pair
  ;; the audit's case: reducing `q` (K-like Eq.rec over kh : ka = kb) inside the Nat shortcut
  ;; compares `ka = kb` with `ka = ka`; that inner lazy delta must not replace the outer pair
  (let [env @nested-env
        motive (lam "x" (c "Nat") (lam "h" (e/app* (c "Eq" [l1]) (c "Nat") (c "ka") (e/bvar 0)) (c "Nat")))
        q (e/app* (c "Eq.rec" (eq-rec-levels env l1 l1)) (c "Nat") (c "ka") motive (c "ka") (c "kb") (c "kh"))]
    (is (defeq? env q (c "ka")))
    (is (false? (defeq? env (e/app (c "Nat.succ") q) (c "ka"))))))

;; ------------------------------------------------------------------ K and metavariables

(deftest k-reduction-ignores-universe-metavariables
  ;; to_cnstr_when_K declines when an index has an *expression* metavariable (has_expr_mvar)
  (let [u (lvl/mvar 7)
        sort-u (e/sort' u)
        alpha (e/sort' (lvl/succ u))
        alpha-level (lvl/succ (lvl/succ u))]
    (testing "a universe metavariable in the index: K applies, the recursor reduces to its minor"
      (let [checker (tc @base)
            _ (.addLocal checker 1 "h" ^Expr (e/app* (c "Eq" [alpha-level]) alpha sort-u sort-u))
            motive (lam "x" alpha (lam "h" (e/app* (c "Eq" [alpha-level]) alpha sort-u (e/bvar 0)) (c "Nat")))
            q (e/app* (c "Eq.rec" (eq-rec-levels @base l1 alpha-level)) alpha sort-u motive (lit 5) sort-u (e/fvar 1))]
        (is (= (str (lit 5)) (str (.whnf (.getReducer checker) q))))))
    (testing "an expression metavariable in the index: K declines and the recursor is stuck"
      (let [checker (tc @base)
            m (e/mvar 3)
            _ (.addLocal checker 1 "h" ^Expr (e/app* (c "Eq" [l1]) (c "Nat") m m))
            motive (lam "x" (c "Nat") (lam "h" (e/app* (c "Eq" [l1]) (c "Nat") m (e/bvar 0)) (c "Nat")))
            q (e/app* (c "Eq.rec" (eq-rec-levels @base l1 l1)) (c "Nat") m motive (lit 5) m (e/fvar 1))]
        (is (same? q (.whnf (.getReducer checker) q)))))))

;; ------------------------------------------------------------------ inference

(deftest inference-returns-the-declared-type
  ;; Lean's infer_type_core does not strip outParam / semiOutParam
  (let [env (env/check-constant @base (env/mk-axiom (n "kOut") [] (e/app (c "outParam" [l1]) (c "Nat"))) fuel)]
    (is (= (str (e/app (c "outParam" [l1]) (c "Nat"))) (str (.inferType (tc env) (c "kOut")))))))

(deftest inference-rejects-loose-bound-variables
  (is (re-find #"loose bound variables"
               (str (kernel-error #(.inferType (tc @base) (e/app (c "Nat.succ") (e/bvar 0)))))))
  (is (re-find #"bound variable index is too big" (str (kernel-error #(Expr/bvar 1048575)))))
  (is (some? (Expr/bvar 1048574)) "range 1048575 fits Lean's 20 bits"))

(deftest dead-lets-are-dropped-from-inferred-types
  ;; local_ctx::mk_binding keeps a let only when its own variable (#0) occurs:
  ;; let x : Type := Nat; let y : Nat := 0; fun z : x => z   :   let x : Type := Nat; x → x
  (let [term (e/let' (n "x") type0 (c "Nat")
                     (e/let' (n "y") (c "Nat") (lit 0)
                             (lam "z" (e/bvar 1) (e/bvar 0))))
        expected (e/let' (n "x") type0 (c "Nat") (pi "z" (e/bvar 0) (e/bvar 1)))
        ty (.inferType (tc @base) term)]
    (is (same? expected ty) (str ty))))

;; ------------------------------------------------------------------ string literals

(def ^:private string-env
  ;; a custom environment in which String.ofList ignores its argument
  (delay
    (let [u (n "u") tu (e/sort' (lvl/succ (lvl/param u)))
          list-u (fn [a] (e/app (c "List" [(lvl/param u)]) a))
          ax (fn [env nm lps ty] (env/add-constant env (env/mk-axiom (n nm) lps ty)))
          env (-> (Env.)
                  (ax "Nat" [] type0) (ax "String" [] type0) (ax "Char" [] type0)
                  (ax "Char.ofNat" [] (pi "n" (c "Nat") (c "Char")))
                  (ax "List" [u] (pi "a" tu tu))
                  (ax "List.nil" [u] (e/forall' (n "a") tu (list-u (e/bvar 0)) :implicit))
                  (ax "List.cons" [u] (e/forall' (n "a") tu (pi "h" (e/bvar 0) (pi "t" (list-u (e/bvar 1)) (list-u (e/bvar 2)))) :implicit))
                  (ax "s0" [] (c "String")))]
      (env/check-constant env (env/mk-def (n "String.ofList") [] (pi "l" (e/app (c "List" [l0]) (c "Char")) (c "String"))
                                          (lam "l" (e/app (c "List" [l0]) (c "Char")) (c "s0")) :hints {:regular 1})
                          fuel))))

(deftest string-literals-expand-only-against-string-of-list
  ;; try_string_lit_expansion_core: the other side must be `String.ofList xs`
  (is (false? (defeq? @string-env (e/lit-str "a") (c "s0")))))

(defn- char-list [cps]
  (reduce (fn [acc cp] (e/app* (c "List.cons" [l0]) (c "Char") (e/app (c "Char.ofNat") (lit cp)) acc))
          (e/app (c "List.nil" [l0]) (c "Char")) (reverse cps)))

(deftest string-literals-expand-by-code-point
  ;; U+1D538 (outside the BMP) is one Char, not two UTF-16 units
  (is (defeq? @base (e/lit-str "𝔸") (e/app (c "String.ofList") (char-list [120120]))))
  (is (false? (defeq? @base (e/lit-str "𝔸") (e/app (c "String.ofList") (char-list [55349 56632]))))))

;; ------------------------------------------------------------------ errors after unfolding

(deftest delta-candidates-have-the-right-universe-arity
  ;; is_delta: kg unfolds to kf.{0}, a wrong-arity application and so no delta candidate; the
  ;; comparison falls through to is_def_eq_unit_like, whose inference rejects it (Lean: error)
  (let [env (env/check-constant @base (env/mk-def (n "kf") [] (c "Nat") (c "Nat.zero") :hints {:regular 5}) fuel)
        env (env/add-constant env (env/mk-def (n "kg") [] (c "Nat") (c "kf" [l0]) :hints {:regular 1}))]
    (is (re-find #"Universe level mismatch for kf"
                 (str (kernel-error #(defeq? env (c "kg") (c "Nat.zero"))))))))

(deftest eta-struct-inference-errors-propagate
  ;; kgS unfolds to the wrong-arity kfS.{0}; against `KS.mk 1` the comparison reaches
  ;; try_eta_struct_core, whose inference of kfS.{0} fails (Lean: error)
  (let [env (env/check-constant @st-env (env/mk-def (n "kfS") [] (c "KS") (e/app (c "KS.mk") (lit 0)) :hints {:regular 5}) fuel)
        env (env/add-constant env (env/mk-def (n "kgS") [] (c "KS") (c "kfS" [l0]) :hints {:regular 1}))]
    (is (re-find #"Universe level mismatch for kfS"
                 (str (kernel-error #(defeq? env (c "kgS") (e/app (c "KS.mk") (lit 1)))))))))

;; ------------------------------------------------------------------ cache invariants

(deftest locals-keep-a-fixed-type
  (let [checker (tc @base)]
    (.addLocal checker 5 "x" ^Expr (c "Nat"))
    (.addLocal checker 5 "x" ^Expr (c "Nat"))
    (is (thrown-with-msg? IllegalArgumentException #"already registered with a different type"
                          (.addLocal checker 5 "x" ^Expr (c "Bool"))))
    (is (thrown-with-msg? IllegalArgumentException #"invalid local id"
                          (.addLocal checker TypeChecker/KERNEL_FRESH_BASE "y" ^Expr (c "Nat"))))
    (let [id (.nextFvarId checker)]
      (.addLocal checker id "z" ^Expr (c "Nat"))
      (is (= (str (c "Nat")) (str (.inferType checker (e/fvar id))))))))

(deftest unfolding-policy-changes-clear-the-conversion-caches
  (let [env (env/check-constant @base (env/mk-def (n "kal") [] (c "Nat") (c "Nat.zero") :hints {:regular 1}) fuel)
        checker (tc env)]
    (is (.isDefEq checker (c "kal") (c "Nat.zero")))
    (.setTransparency checker 0)
    (is (false? (.isDefEq checker (c "kal") (c "Nat.zero"))) "the earlier success is not reused")
    (.setDeltaAllowSet checker (java.util.HashSet. [(n "kal")]))
    (is (.isDefEq checker (c "kal") (c "Nat.zero")))))

;; ------------------------------------------------------------------ the Clojure reducer

(deftest the-clojure-reducer-shares-the-kernel-rules
  (testing "a constructor of another structure is not projected"
    (let [term (e/proj (n "KS") 0 (e/app (c "KT.mk") (lit 1)))]
      (is (same? term (red/whnf @st-env term)))))
  (testing "Nat primitives are complete constants, computed by the kernel's primitive"
    (let [reduce-nat #'red/try-reduce-nat
          lits [(lit 2) (lit 3)]
          w identity]
      (is (nil? (reduce-nat (c "Nat.add" [l0]) lits w)))
      (is (= (str (lit 5)) (str (reduce-nat (c "Nat.add") lits w))))
      (is (thrown-with-msg? RuntimeException #"does not fit in a 32-bit unsigned integer"
                            (reduce-nat (c "Nat.pow") [(lit 1) (lit 4294967296)] w))))))

(deftest structure-eta-can-be-turned-off-for-meta-callers
  ;; to_cnstr_when_structure expands a structure-typed major `p` to `mk p.1 p.2`; meta-level
  ;; callers that read recursor applications (the WF encoder) turn it off, like Lean's
  ;; Meta.Config.etaStruct
  (let [prod-nn (e/app* (c "Prod" [l0 l0]) (c "Nat") (c "Nat"))
        motive (lam "q" prod-nn (c "Nat"))
        minor (lam "a" (c "Nat") (lam "b" (c "Nat") (e/bvar 1)))
        term (e/app* (c "Prod.casesOn" [l1 l0 l0]) (c "Nat") (c "Nat") motive (e/fvar 1) minor)
        reduce-with (fn [eta?]
                      (let [checker (tc @base)]
                        (.addLocal checker 1 "p" ^Expr prod-nn)
                        (.setStructureEta (.getReducer checker) eta?)
                        (.whnf (.getReducer checker) term)))]
    (is (same? (e/proj (n "Prod") 0 (e/fvar 1)) (reduce-with true)))
    (is (= (n "Prod.rec") (e/const-name (e/get-app-fn (reduce-with false)))))))

;; ------------------------------------------------------------------ K2 verification round

(deftest the-clojure-reducer-follows-the-kernel-through-its-public-whnf
  (testing "Nat.succ.{0} is not the successor (every path matches complete constants)"
    (let [term (e/app (c "Nat.succ" [l0]) (lit 2))]
      (is (same? term (red/whnf @base term)))))
  (testing "a definition applied to the wrong universe arity is not unfolded"
    (let [term (e/app* (c "Nat.add" [l0]) (lit 2) (lit 3))]
      (is (same? term (red/whnf @base term)))))
  (testing "a projection of an unknown constant is an error (env.get)"
    (is (re-find #"Unknown constant: KMissing"
                 (str (kernel-error #(red/whnf @st-env (e/proj (n "KS") 0 (c "KMissing"))))))))
  (testing "the let-local fallback of tc/is-def-eq does not accept Nat.succ.{0} 2 = 3"
    (let [st (ktc/attach-lctx (ktc/mk-tc-state @base)
                              (red/lctx-add-let (red/empty-lctx) 7 "v" (c "Nat") (lit 0)))]
      (is (nil? (ktc/java-tc st)) "a let-local sends the comparison to the Clojure fallback")
      (is (not (true? (try (ktc/is-def-eq st (e/app (c "Nat.succ" [l0]) (lit 2)) (lit 3))
                           (catch Exception _ :error)))))
      (is (true? (ktc/is-def-eq st (e/app (c "Nat.succ") (lit 2)) (lit 3)))))))

(deftest cache-inputs-cannot-change-under-the-caches
  (let [env (env/check-constant @base (env/mk-def (n "kal2") [] (c "Nat") (c "Nat.zero") :hints {:regular 1}) fuel)
        checker (tc env)
        allow (java.util.HashSet. [(n "kal2")])]
    (.setTransparency checker 0)
    (.setDeltaAllowSet checker allow)
    (is (.isDefEq checker (c "kal2") (c "Nat.zero")))
    (testing "the allow-set is copied: changing the caller's set changes nothing"
      (.remove allow (n "kal2"))
      (is (.canUnfold (.getReducer checker) (n "kal2")))
      (is (.isDefEq checker (c "kal2") (c "Nat.zero"))))
    (testing "the local context is not exposed: lookupFvar hands out a copy"
      (.addLocal checker 3 "x" ^Expr (c "Nat"))
      (aset ^objects (.lookupFvar checker 3) 2 (c "Bool"))
      (is (= (str (c "Nat")) (str (.inferType checker (e/fvar 3))))))))

(deftest nat-pow-representability-is-decided-exactly
  ;; decided without computing the power
  (is (= 1 (Reducer/powRepresentability (biginteger 2) 1073741824)) "2^(2^30): 2^30 + 1 bits fit")
  (is (= -1 (Reducer/powRepresentability (biginteger 2) 2147483647)) "2^(2^31 - 1) needs 2^31 bits")
  (is (= 1 (Reducer/powRepresentability (biginteger 3) 1354911328)) "3^k with 2^31 - 1 bits fits")
  (is (= -1 (Reducer/powRepresentability (biginteger 3) 1354911331)))
  (is (thrown-with-msg? RuntimeException #"cannot be represented"
                        (Reducer/natBinop Name/NAT_POW (biginteger 2) (biginteger 2147483647) -1))
      "a proven overflow is refused before any allocation"))

;; ------------------------------------------------------------------ K2 follow-up review

(deftest universe-lists-are-immutable-through-the-public-fields
  ;; p, q : P.{0} are proofs (P.{u} : Sort u), so p ≡ q by proof irrelevance; a caller
  ;; must not be able to turn the cached type into P.{1}
  (let [u (n "u")
        env (env/check-constant @base (env/mk-axiom (n "KP") [u] (e/sort' (lvl/param u))) fuel)
        lv (object-array [l0])
        p-ty (Expr/mkConst (n "KP") lv)
        checker (tc env)]
    (aset lv 0 l1)
    (is (same? (c "KP" [l0]) p-ty) "the caller's array is copied")
    (.addLocal checker 1 "p" ^Expr p-ty)
    (.addLocal checker 2 "q" ^Expr p-ty)
    (is (.isDefEq checker (e/fvar 1) (e/fvar 2)))
    (let [^Expr ty (aget ^objects (.lookupFvar checker 1) 2)]
      (is (thrown? UnsupportedOperationException (.set ^java.util.List (.o1 ty) 0 l1))))
    (is (same? (c "KP" [l0]) (.inferType checker (e/fvar 1))))
    (is (.isDefEq checker (e/fvar 1) (e/fvar 2)))))

(deftest nat-results-are-refused-only-when-they-do-not-fit
  ;; with a 10-bit limit standing in for the JVM's 2^31 - 1
  (let [add #(Reducer/natBinop Name/NAT_ADD (biginteger %1) (biginteger %2) Reducer/NAT_MAX_BYTES_DEFAULT 10)
        pow #(Reducer/natBinop Name/NAT_POW (biginteger %1) (biginteger %2) Reducer/NAT_MAX_BYTES_DEFAULT 100)]
    (is (= (str (lit 513)) (str (add 512 1))) "2^9 + 1 keeps 10 bits")
    (is (thrown-with-msg? RuntimeException #"cannot be represented" (add 1023 1)) "2^10 needs 11 bits")
    (testing "pow inside the estimate's margin is decided by the result"
      (is (= 1 (Reducer/powRepresentability (biginteger 3) 64 100)) "3^64 (102 bits) is in the margin")
      (is (thrown-with-msg? RuntimeException #"cannot be represented" (pow 3 64)))
      (is (= 100 (.bitLength ^BigInteger (e/lit-nat-val (pow 3 63)))) "3^63 has exactly 100 bits"))))

(deftest the-clojure-reducer-forces-the-right-operand-only-after-a-literal-left
  ;; reduce_bin_nat_op returns as soon as the left operand is not a literal; the right one here
  ;; would be an error (a projection of an unknown constant)
  (let [no-delta {:can-unfold? (constantly false)}
        bad (e/proj (n "KS") 0 (c "KMissing"))
        term (e/app* (c "Nat.add") (e/fvar 1) bad)]
    (is (same? term (red/whnf @st-env term nil no-delta)))
    (is (re-find #"Unknown constant: KMissing"
                 (str (kernel-error #(red/whnf @st-env (e/app* (c "Nat.add") (lit 1) bad) nil no-delta)))))))

(deftest the-clojure-projection-guard-is-unsigned-32-bit
  (is (re-find #"Unknown constant: KMissing"
               (str (kernel-error #(red/whnf @st-env (e/proj (n "KS") 2147483648 (c "KMissing"))))))
      "2^31 is a valid index: the constructor is looked up")
  (let [term (e/proj (n "KS") 4294967296 (c "KMissing"))]
    (is (same? term (red/whnf @st-env term)) "2^32 is no projection index")))

(deftest the-clojure-reducer-checks-recursor-universe-arity
  (let [motive (lam "n" (c "Nat") (c "Nat"))
        rec (fn [ls] (e/app* (c "Nat.rec" ls) motive (lit 7) (lam "n" (c "Nat") (lam "ih" (c "Nat") (e/bvar 0))) (lit 0)))]
    (is (= (str (lit 7)) (str (red/whnf @base (rec [l1])))))
    (is (same? (rec []) (red/whnf @base (rec [])))
        "Nat.rec applied to no universes is not reduced")))
