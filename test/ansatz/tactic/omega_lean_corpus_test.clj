(ns ansatz.tactic.omega-lean-corpus-test
  "Regression corpus for the `omega` tactic, transcribed from lean4's own
   `tests/lean/run/omega.lean` (the Nat/Int LINEAR subset).

   Everything here is driven through the USER-FACING entry point
   `ansatz.tactic.omega/omega` — the same function `(omega)` resolves to in the
   surface tactic block (ansatz.core:880) — and every solved goal is re-checked
   with the STRICT kernel checker via `extract/verify`. Driving the internal
   proof-producing engine (`ansatz.tactic.omega-proof/omega`) directly would hide
   the front-end gate, which is exactly where regressions live.

   Environment: the Init tier ansatz SHIPS — resources/ansatz/init-medium.ndjson.gz,
   the dependency closure of scripts/init-store-roots.txt — NOT Mathlib, and NOT a
   `test-data/` fixture. omega's proof reconstruction depends on `Init.Omega`, so the
   whole corpus must run on that env; anything it still cannot decide is called out
   explicitly below rather than silently skipped.

   Out of scope here (matching what the tactic does not implement): `Fin`,
   `BitVec`, `min`/`max`, if-then-else splitting, `Int.natAbs`, `Int.toNat`,
   divisibility (`∣`), `2^n`, `Prod.Lex`, and existentials/subtypes.

   Goals are built as kernel `Expr`s rather than surface forms so that the exact
   SPELLING under test is controlled: the ansatz surface elaborates arithmetic to
   BARE `Nat.add`/`Nat.sub`/`Nat.mul`/`Nat.div`/`Nat.mod` (ansatz.surface.ingest
   `arith-lift`), while goals coming from Lean's own library carry the
   `HAdd.hAdd`/`HDiv.hDiv` typeclass spelling. omega must decide both
   identically, so both are exercised."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.omega :as omega]
            ;; for *strict-div-bounds* — see int-div-bounds-are-emitted
            [ansatz.tactic.omega-proof :as omega-proof]))

;; ============================================================
;; Environment
;; ============================================================

(defn- require-env []
  @test-env/bundled-init-env)

;; ============================================================
;; Expression builders
;; ============================================================

(def ^:private u1 (lvl/succ lvl/zero))
(defn- c [s] (e/const' (name/from-string s) []))
(defn- c1 [s] (e/const' (name/from-string s) [lvl/zero]))
(defn- c3 [s] (e/const' (name/from-string s) [lvl/zero lvl/zero lvl/zero]))

(def ^:private NAT (c "Nat"))
(def ^:private INT (c "Int"))
(def ^:private FALSE (c "False"))
(def ^:private TRUE (c "True"))

(defn- nlit [k] (e/lit-nat k))

;; --- bare Nat spelling (what the ansatz surface emits) ---
(defn- n+ [a b] (e/app* (c "Nat.add") a b))
(defn- n- [a b] (e/app* (c "Nat.sub") a b))
(defn- n* [a b] (e/app* (c "Nat.mul") a b))
(defn- ndiv [a b] (e/app* (c "Nat.div") a b))
(defn- nmod [a b] (e/app* (c "Nat.mod") a b))
(defn- nsucc [a] (e/app (c "Nat.succ") a))

;; --- HXxx (typeclass) spelling ---
(defn- hbin [op inst T a b]
  (e/app* (c3 op) T T T (e/app* (c1 (str "instH" (subs op 1 (.indexOf ^String op ".")))) T (c inst)) a b))
(defn- h+  [a b] (hbin "HAdd.hAdd" "instAddNat" NAT a b))
(defn- h*  [a b] (hbin "HMul.hMul" "instMulNat" NAT a b))
(defn- hdiv [a b] (hbin "HDiv.hDiv" "Nat.instDiv" NAT a b))
(defn- hmod [a b] (hbin "HMod.hMod" "Nat.instMod" NAT a b))

;; --- Int (always the typeclass spelling; Int has no bare-op surface) ---
(defn- ilit
  "Int literal. Negative values go through Int.negSucc (the surface has no negative
   integer literal — ansatz.surface.elaborate maps every integer literal to lit-nat)."
  [k]
  (if (neg? k)
    (e/app (c "Int.negSucc") (nlit (dec (- k))))
    (e/app (c "Int.ofNat") (nlit k))))
(defn- i+ [a b] (hbin "HAdd.hAdd" "Int.instAdd" INT a b))
(defn- i- [a b] (hbin "HSub.hSub" "Int.instSub" INT a b))
(defn- i* [a b] (hbin "HMul.hMul" "Int.instMul" INT a b))
(defn- idiv [a b] (hbin "HDiv.hDiv" "Int.instDiv" INT a b))
(defn- imod [a b] (hbin "HMod.hMod" "Int.instMod" INT a b))
(defn- ineg [a] (e/app* (c "Neg.neg") INT (c "Int.instNegInt") a))

;; --- propositions ---
(defn- le* [T inst a b] (e/app* (c1 "LE.le") T (c inst) a b))
(defn- lt* [T inst a b] (e/app* (c1 "LT.lt") T (c inst) a b))
(defn- n<= [a b] (le* NAT "instLENat" a b))
(defn- n<  [a b] (lt* NAT "instLTNat" a b))
(defn- n=  [a b] (e/app* (e/const' (name/from-string "Eq") [u1]) NAT a b))
(defn- i<= [a b] (le* INT "Int.instLEInt" a b))
(defn- i<  [a b] (lt* INT "Int.instLTInt" a b))
(defn- i=  [a b] (e/app* (e/const' (name/from-string "Eq") [u1]) INT a b))
(defn- p-not [p] (e/app (c "Not") p))
(defn- p-and [p q] (e/app* (c "And") p q))
(defn- p-or  [p q] (e/app* (c "Or") p q))
(defn- p-imp [p q] (e/arrow p q))
(defn- p-iff [p q] (e/app* (c "Iff") p q))
(defn- n-ne [a b] (e/app* (e/const' (name/from-string "Ne") [u1]) NAT a b))
(defn- i-ne [a b] (e/app* (e/const' (name/from-string "Ne") [u1]) INT a b))

;; --- min / max ---
(defn- nmin [a b] (e/app* (c1 "Min.min") NAT (c "instMinNat") a b))
(defn- imin [a b] (e/app* (c1 "Min.min") INT (c "Int.instMin") a b))
(defn- imax [a b] (e/app* (c1 "Max.max") INT (c "Int.instMax") a b))

;; --- Bool comparisons (the Bool→Prop bridge) ---
(defn- b= [lhs rhs] (e/app* (e/const' (name/from-string "Eq") [u1]) (c "Bool") lhs rhs))
(defn- ble [a b] (e/app* (c "Nat.ble") a b))
(defn- blt [a b] (e/app* (c "Nat.blt") a b))
(def ^:private BTRUE  (c "Bool.true"))
(def ^:private BFALSE (c "Bool.false"))

;; ============================================================
;; Goal assembly
;; ============================================================
;;
;; Lean's `example (x y : Nat) (h₁ : P) (h₂ : Q) : R` becomes
;;   (ex [["x" NAT] ["y" NAT]] (fn [x y] {:hyps [P Q] :concl R}))
;; which builds the CLOSED goal `∀ x y, P → Q → R`, then intros everything —
;; exactly what `a/theorem` does (ansatz.core/prove-theorem).

(def ^:private fvar-counter (atom 0))
(defn- fresh-id! [] (swap! fvar-counter inc))

(defn- ex
  "Build [goal-type intro-names] for a transcribed Lean `example`."
  [binders body-fn]
  (let [ids (mapv (fn [_] (fresh-id!)) binders)
        {:keys [hyps concl]} (apply body-fn (map e/fvar ids))
        hyps (vec hyps)
        ;; hypotheses and conclusion mention only fvars, so no de Bruijn lifting
        ;; is needed while stacking the (non-dependent) arrows.
        body (reduce (fn [acc h] (e/arrow h acc)) concl (reverse hyps))
        goal (reduce (fn [acc [[bname btype] id]]
                       (e/forall' bname btype (e/abstract1 acc id) :default))
                     body
                     (reverse (map vector binders ids)))
        names (into (mapv first binders)
                    (map #(str "h" %) (range (count hyps))))]
    [goal names]))

(defn- run-omega
  "Run the user-facing omega on a transcribed example.
   Returns :ok (solved AND kernel-verified), :unsolved, or [:err message]."
  [[goal names]]
  (let [env (require-env)]
    (try
      (let [[ps _] (proof/start-proof env goal)
            ps (if (seq names) (basic/intros ps names) ps)
            ps (omega/omega ps)]
        (if (proof/solved? ps)
          (do (extract/verify ps) :ok)
          :unsolved))
      (catch Throwable t [:err (.getMessage t)]))))

(defn- proves
  "Assert omega closes `example` with a kernel-checked proof term."
  [label example]
  (is (= :ok (run-omega example)) label))

(defn- rejects
  "Assert omega does NOT close `example` — lean4's `fail_if_success omega`."
  [label example]
  (is (not= :ok (run-omega example)) label))

(defn- gap
  "A lean4 corpus entry this port does not decide YET. Reported, never asserted, so
   the corpus stays a complete transcription without turning a known gap into a red
   build. `why` names the blocker. If it ever starts passing the run prints a NOTE
   telling you to promote it to `proves` — that is how the div/mod entries below got
   promoted."
  [label why example]
  (let [r (run-omega example)]
    (when (= :ok r)
      (println "  NOTE: gap entry now PASSES —" label "— promote it to `proves` (" why ")"))
    (is true label)))

(defn- divergence
  "A lean4 corpus entry where this port deliberately behaves differently. Documented,
   never asserted."
  [label _why example]
  (run-omega example)
  (is true label))

;; ============================================================
;; Nat — linear, no division
;; ============================================================

(deftest corpus-nat-linear
  (testing "lean4 omega.lean — Nat linear fragment"
    ;; L29 / L30: ground contradictory hypotheses
    (proves "(7 < 3) → False"
            (ex [] (fn [] {:hyps [(n< (nlit 7) (nlit 3))] :concl FALSE})))
    (proves "(0 < 0) → False"
            (ex [] (fn [] {:hyps [(n< (nlit 0) (nlit 0))] :concl FALSE})))
    ;; L32 / L33
    (proves "x > 7 → x < 3 → False"
            (ex [["x" NAT]] (fn [x] {:hyps [(n< (nlit 7) x) (n< x (nlit 3))] :concl FALSE})))
    (proves "x ≥ 7 → x ≤ 3 → False"
            (ex [["x" NAT]] (fn [x] {:hyps [(n<= (nlit 7) x) (n<= x (nlit 3))] :concl FALSE})))
    ;; L35
    (proves "x + y > 10 → x < 5 → y < 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n< (nlit 10) (n+ x y)) (n< x (nlit 5)) (n< y (nlit 5))]
                           :concl FALSE})))
    ;; L38
    (proves "x + y > 10 → 2*x < 11 → y < 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n< (nlit 10) (n+ x y))
                                  (n< (n* (nlit 2) x) (nlit 11))
                                  (n< y (nlit 5))]
                           :concl FALSE})))
    ;; L41 — gcd tightening: 2 ∤ 5
    (proves "2*x + 4*y = 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= (n+ (n* (nlit 2) x) (n* (nlit 4) y)) (nlit 5))] :concl FALSE})))
    ;; L48 / L50 — nested ground multiplication. 6x + 7y = 5 needs integrality; see
    ;; corpus-nat-integrality below.
    (proves "2*(3*x) + y*7 = 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= (n+ (n* (nlit 2) (n* (nlit 3) x)) (n* y (nlit 7))) (nlit 5))]
                           :concl FALSE})))
    ;; L52
    (proves "x < 0 → False"
            (ex [["x" NAT]] (fn [x] {:hyps [(n< x (nlit 0))] :concl FALSE})))
    ;; L80
    (proves "5 ≤ x → x ≤ 4 → False"
            (ex [["x" NAT]] (fn [x] {:hyps [(n<= (nlit 5) x) (n<= x (nlit 4))] :concl FALSE})))
    ;; L233
    (proves "b + 2 > 3 + b → False"
            (ex [["b" NAT]]
                (fn [b] {:hyps [(n< (n+ (nlit 3) b) (n+ b (nlit 2)))] :concl FALSE})))
    ;; L27
    (proves "a ≤ c → b ≤ c → a < succ c"
            (ex [["a" NAT] ["b" NAT] ["c" NAT]]
                (fn [a b c] {:hyps [(n<= a c) (n<= b c)] :concl (n< a (nsucc c))})))
    ;; L296
    (proves "i ≤ n → i < n + 1"
            (ex [["i" NAT] ["n" NAT]]
                (fn [i n] {:hyps [(n<= i n)] :concl (n< i (n+ n (nlit 1)))})))
    ;; L290
    (proves "p + n' = p' + n → n + p' = n' + p"
            (ex [["p" NAT] ["n" NAT] ["p'" NAT] ["n'" NAT]]
                (fn [p n p' n'] {:hyps [(n= (n+ p n') (n+ p' n))]
                                 :concl (n= (n+ n p') (n+ n' p))})))
    ;; L300
    (proves "0 = 0" (ex [] (fn [] {:hyps [] :concl (n= (nlit 0) (nlit 0))})))
    ;; L280 — contradictory ground hypothesis closes an arbitrary arithmetic goal
    (proves "(2 > 3) → a + b - c ≥ 3"
            (ex [["a" NAT] ["b" NAT] ["c" NAT]]
                (fn [a b c] {:hyps [(n< (nlit 3) (nlit 2))]
                             :concl (n<= (nlit 3) (n- (n+ a b) c))})))
    ;; L390 / L391 / L402 — nonlinear products are atomised; Nat atoms are ≥ 0
    (proves "n*n ≥ 0" (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n<= (nlit 0) (n* n n))})))
    (proves "n*n + n ≥ 0"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n<= (nlit 0) (n+ (n* n n) n))})))
    ;; L402
    (gap "a * 1 = a"
         "the k=1 shortcut in mk-scale-eval-proof returns the operand's eval proof unchanged,
          so the proof claims `lc.eval = ↑a` while the goal needs `↑(a * 1)`; `Nat.mul a 1`
          is NOT definitionally `a` (Nat.mul recurses on its second argument), so the bridge
          has to go through Nat.mul_one"
         (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n= (n* a (nlit 1)) a)})))
    ;; L394 / L395 / L396
    (proves "n * 2 = n + n"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n= (n* n (nlit 2)) (n+ n n))})))
    (proves "n*n * 2 = n*n + n*n"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n= (n* (n* n n) (nlit 2))
                                                         (n+ (n* n n) (n* n n)))})))
    (proves "2 * (n*n) = n*n + n*n"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n= (n* (nlit 2) (n* n n))
                                                         (n+ (n* n n) (n* n n)))})))
    ;; L25
    (proves "x ≠ 0 → 0 < x"
            (ex [["x" NAT]] (fn [x] {:hyps [(n-ne x (nlit 0))] :concl (n< (nlit 0) x)})))))

(deftest corpus-nat-truncated-sub
  (testing "lean4 omega.lean — truncated Nat subtraction (the a-b dichotomy)"
    ;; L56
    (proves "x - y = 0 → x > y → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= (n- x y) (nlit 0)) (n< y x)] :concl FALSE})))
    ;; L68
    (proves "x - y ≤ 0 → y < x → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n<= (n- x y) (nlit 0)) (n< y x)] :concl FALSE})))
    ;; L62
    (proves "x - y - z = 0 → x > y + z → False"
            (ex [["x" NAT] ["y" NAT] ["z" NAT]]
                (fn [x y z] {:hyps [(n= (n- (n- x y) z) (nlit 0)) (n< (n+ y z) x)]
                             :concl FALSE})))
    ;; L392
    (proves "i*j + k + l - k = i*j + l"
            (ex [["i" NAT] ["j" NAT] ["k" NAT] ["l" NAT]]
                (fn [i j k l] {:hyps []
                               :concl (n= (n- (n+ (n+ (n* i j) k) l) k)
                                          (n+ (n* i j) l))})))
    ;; L86 — nested truncated subtraction, two dichotomies split jointly
    (proves "a - (b - c) ≤ 5 → b ≥ c + 3 → a + c ≥ b + 6 → False"
            (ex [["a" NAT] ["b" NAT] ["c" NAT]]
                (fn [a b c] {:hyps [(n<= (n- a (n- b c)) (nlit 5))
                                    (n<= (n+ c (nlit 3)) b)
                                    (n<= (n+ b (nlit 6)) (n+ a c))]
                             :concl FALSE})))
    ;; L64 — five chained truncated subtractions
    (proves "a-b-c-d-e-f = 0 → a > b+c+d+e+f → False"
            (ex [["a" NAT] ["b" NAT] ["c" NAT] ["d" NAT] ["e" NAT] ["f" NAT]]
                (fn [a b c d e f]
                  {:hyps [(n= (n- (n- (n- (n- (n- a b) c) d) e) f) (nlit 0))
                          (n< (n+ (n+ (n+ (n+ b c) d) e) f) a)]
                   :concl FALSE})))))

(deftest corpus-nat-integrality
  (testing "lean4 omega.lean — entries needing INTEGER (not rational) reasoning"
    ;; L45 / L47 — the real relaxation of 6x+7y=5 is satisfiable (x = 5/6), so deciding
    ;; it needs `bmod` ("balanced mod") hard-equality elimination: an equality none of
    ;; whose coefficients is ±1 cannot be removed by substitution, so `solve-hard-equality`
    ;; introduces a fresh atom `bmod_div_term m x v` and a smaller equality in its place,
    ;; and `Lean.Omega.bmod_sat` certifies the step.
    (proves "6*x + 7*y = 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= (n+ (n* (nlit 6) x) (n* (nlit 7) y)) (nlit 5))]
                           :concl FALSE})))
    (proves "x*6 + y*7 = 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= (n+ (n* x (nlit 6)) (n* y (nlit 7))) (nlit 5))]
                           :concl FALSE})))
    ;; NOT from lean4's corpus. `m = minNatAbs + 1` is EVEN here (min |coeff| = 3), and
    ;; `Int.bmod`'s range is asymmetric for even m — `-Int.bmod (-r) m ≠ Int.bmod r m`
    ;; when `r ≡ m/2`. The bmod step used to negate `r`, which is why this needs its own
    ;; entry rather than riding on the two odd-m cases above. It also takes TWO hard
    ;; equalities (m = 4, then m = 3), so it exercises the loop, not just one step.
    (proves "3*x + 5*y = 4 → False  (even bmod modulus, two hard-equality rounds)"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= (n+ (n* (nlit 3) x) (n* (nlit 5) y)) (nlit 4))]
                           :concl FALSE})))))

(deftest hard-equality-actually-fires
  (testing "the bmod route is what decides 6x+7y=5 — not some other elimination"
    ;; Without this, `corpus-nat-integrality` above would still pass if the solver
    ;; happened to find a rational refutation, and the bmod proof path could rot
    ;; unnoticed exactly as it did before. `solve-hard-equality` is private, so reach
    ;; it through its Var.
    (let [v (ns-resolve 'ansatz.tactic.omega.fm 'solve-hard-equality)
          orig @v
          calls (atom [])]
      (with-redefs-fn {v (fn [table problem coeffs-key f g]
                           (let [fact (get-in problem [:constraints coeffs-key])]
                             (swap! calls conj [(vec (:coeffs fact))
                                                (:lower (:constraint fact))]))
                           (orig table problem coeffs-key f g))}
        (fn []
          (is (= :ok (run-omega
                      (ex [["x" NAT] ["y" NAT]]
                          (fn [x y] {:hyps [(n= (n+ (n* (nlit 6) x) (n* (nlit 7) y)) (nlit 5))]
                                     :concl FALSE}))))
              "6x + 7y = 5 → False, kernel-checked")))
      (is (= [[[6 7] 5]] (mapv (fn [[cs l]] [(mapv long cs) (long l)]) @calls))
          (str "solve-hard-equality must run exactly once, on the coefficients [6 7] "
               "with r = 5 — `r` is the constraint's own bound, in dot-product units, "
               "NOT its negation (that mismatch is what `bmod_sat` rejected). Saw: "
               (pr-str @calls))))))

;; ============================================================
;; Nat — division and modulo (the feature under test)
;; ============================================================

(deftest corpus-nat-div-bare-spelling
  (testing "bare Nat.div / Nat.mod — the spelling the ansatz surface emits"
    ;; the two facts Lean's analyzeAtom attaches to a quotient atom
    (proves "a / 3 * 3 ≤ a"
            (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n<= (n* (ndiv a (nlit 3)) (nlit 3)) a)})))
    (proves "a < (a / 3 + 1) * 3"
            (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n< a (n* (n+ (ndiv a (nlit 3)) (nlit 1))
                                                               (nlit 3)))})))
    (proves "a % 3 < 3"
            (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n< (nmod a (nlit 3)) (nlit 3))})))
    (proves "a % 3 + a / 3 * 3 = a"
            (ex [["a" NAT]] (fn [a] {:hyps []
                                     :concl (n= (n+ (nmod a (nlit 3)) (n* (ndiv a (nlit 3)) (nlit 3)))
                                                a)})))
    ;; L82
    (proves "x / 3 ≥ 2 → x < 6 → False"
            (ex [["x" NAT]] (fn [x] {:hyps [(n<= (nlit 2) (ndiv x (nlit 3))) (n< x (nlit 6))]
                                     :concl FALSE})))
    ;; L90
    (proves "(x + 4) / 2 ≤ x + 2"
            (ex [["x" NAT]] (fn [x] {:hyps [] :concl (n<= (ndiv (n+ x (nlit 4)) (nlit 2))
                                                          (n+ x (nlit 2)))})))
    ;; L20 — division by the literal 0
    (proves "x / 0 = 0"
            (ex [["x" NAT]] (fn [x] {:hyps [] :concl (n= (ndiv x (nlit 0)) (nlit 0))})))
    (proves "x % 0 = x"
            (ex [["x" NAT]] (fn [x] {:hyps [] :concl (n= (nmod x (nlit 0)) x)})))))

(deftest corpus-nat-div-typeclass-spelling
  (testing "HDiv.hDiv / HMod.hMod — the spelling Lean's own library carries"
    (proves "a / 3 * 3 ≤ a"
            (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n<= (h* (hdiv a (nlit 3)) (nlit 3)) a)})))
    (proves "a < (a / 3 + 1) * 3"
            (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n< a (h* (h+ (hdiv a (nlit 3)) (nlit 1))
                                                               (nlit 3)))})))
    (proves "a % 3 < 3"
            (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n< (hmod a (nlit 3)) (nlit 3))})))
    (proves "a % 3 + a / 3 * 3 = a"
            (ex [["a" NAT]] (fn [a] {:hyps []
                                     :concl (n= (h+ (hmod a (nlit 3)) (h* (hdiv a (nlit 3)) (nlit 3)))
                                                a)})))
    (testing "the two spellings decide the SAME goal identically"
      (proves "mixed spelling: Nat.div a 3 * 3 ≤ HDiv a 3 * 3"
              (ex [["a" NAT]]
                  (fn [a] {:hyps [] :concl (n<= (n* (ndiv a (nlit 3)) (nlit 3))
                                                (h* (hdiv a (nlit 3)) (nlit 3)))}))))))

(deftest corpus-nat-div-harder
  (testing "lean4 omega.lean — division entries beyond the single-atom bounds"
    ;; L72 / L74 — truncated Nat subtraction of two quotients
    (proves "x/2 - y/3 < 1 → 3*x ≥ 2*y + 6 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n< (n- (ndiv x (nlit 2)) (ndiv y (nlit 3))) (nlit 1))
                                  (n<= (n+ (n* (nlit 2) y) (nlit 6)) (n* (nlit 3) x))]
                           :concl FALSE})))
    ;; L170 — truncated subtraction of two remainders
    (proves "x % 4 - x % 8 = 0"
            (ex [["x" NAT]]
                (fn [x] {:hyps [] :concl (n= (n- (nmod x (nlit 4)) (nmod x (nlit 8))) (nlit 0))})))
    ;; L172 — truncated subtraction INSIDE the dividend of a remainder
    (proves "n > 0 → (2*n - 1) % 2 = 1"
            (ex [["n" NAT]]
                (fn [n] {:hyps [(n< (nlit 0) n)]
                         :concl (n= (nmod (n- (n* (nlit 2) n) (nlit 1)) (nlit 2)) (nlit 1))})))
    ;; L215 — quotient of a nonlinear (atomised) product
    (proves "7 < A*B → 0 < A*B/8"
            (ex [["A" NAT] ["B" NAT]]
                (fn [A B] {:hyps [(n< (nlit 7) (n* A B))]
                           :concl (n< (nlit 0) (ndiv (n* A B) (nlit 8)))})))
    ;; L378 — SYMBOLIC divisor. lean4 case-splits on b = 0; we leave `a % b` an
    ;; unconstrained atom, but the goal is still refuted (a % b + 1 = 0 forces the
    ;; Nat atom negative).
    (proves "a % b + 1 = 0 → False"
            (ex [["a" NAT] ["b" NAT]]
                (fn [a b] {:hyps [(n= (n+ (nmod a b) (nlit 1)) (nlit 0))] :concl FALSE})))))

;; ============================================================
;; The BFT quorum-intersection lemma (the acceptance criterion)
;; ============================================================

(deftest quorum-intersection
  (testing "n + ⌊(n-1)/3⌋ < 2*(⌊2n/3⌋ + 1) — BFT quorum intersection, bare Nat.div spelling"
    ;; quorum-size n   = 2n/3 + 1
    ;; byz-tolerance n = (n-1)/3
    (proves "n + (n-1)/3 < 2 * ((2*n)/3 + 1)"
            (ex [["n" NAT]]
                (fn [n] {:hyps []
                         :concl (n< (n+ n (ndiv (n- n (nlit 1)) (nlit 3)))
                                    (n* (nlit 2) (n+ (ndiv (n* (nlit 2) n) (nlit 3)) (nlit 1))))})))))

(deftest quorum-intersection-through-definitions
  (testing "the acceptance case as it is actually WRITTEN — the statement is stated over two
            `a/defn` definitions, so omega has to delta-step THROUGH them to see the divisions
            at all. A blanket whnf would unfold straight past Nat.div into a stuck brecOn blob
            and atomise the quotient."
    (let [nat-arrow-nat (e/forall' "n" NAT NAT :default)
          mk-fn (fn [nm body-fn]
                  (env/mk-def (name/from-string nm) [] nat-arrow-nat
                              (e/lam "n" NAT (body-fn (e/bvar 0)) :default)))
          ;; quorum-size n   = (2 * n) / 3 + 1
          ;; byz-tolerance n = (n - 1) / 3
          env (-> (require-env)
                  (env/check-constant
                   (mk-fn "corpus.quorumSize"
                          (fn [n] (n+ (ndiv (n* (nlit 2) n) (nlit 3)) (nlit 1)))))
                  (env/check-constant
                   (mk-fn "corpus.byzTolerance"
                          (fn [n] (ndiv (n- n (nlit 1)) (nlit 3))))))
          call (fn [nm x] (e/app (c nm) x))
          [goal names] (ex [["n" NAT]]
                           (fn [n] {:hyps []
                                    :concl (n< (n+ n (call "corpus.byzTolerance" n))
                                               (n* (nlit 2) (call "corpus.quorumSize" n)))}))]
      (is (= :ok (let [[ps _] (proof/start-proof env goal)
                       ps (basic/intros ps names)
                       ps (omega/omega ps)]
                   (if (proof/solved? ps) (do (extract/verify ps) :ok) :unsolved)))
          "n + byzTolerance n < 2 * quorumSize n"))))

(deftest div-of-truncated-sub
  (testing "a quotient whose DIVIDEND is a truncated subtraction (the sharp case)"
    ;; This is the shape `byz-tolerance n = (n-1)/3` puts in front of omega: the
    ;; dividend is a `:nat-sub-atoms` atom carrying a deferred dichotomy, and the
    ;; div bounds are stated over that atom.
    (proves "(n - 1) / 3 * 3 ≤ n - 1"
            (ex [["n" NAT]]
                (fn [n] {:hyps [] :concl (n<= (n* (ndiv (n- n (nlit 1)) (nlit 3)) (nlit 3))
                                              (n- n (nlit 1)))})))
    (proves "(n - 1) / 3 ≤ n"
            (ex [["n" NAT]]
                (fn [n] {:hyps [] :concl (n<= (ndiv (n- n (nlit 1)) (nlit 3)) n)})))
    (proves "1 ≤ n → 3 * ((n-1)/3) ≤ n - 1"
            (ex [["n" NAT]]
                (fn [n] {:hyps [(n<= (nlit 1) n)]
                         :concl (n<= (n* (nlit 3) (ndiv (n- n (nlit 1)) (nlit 3)))
                                     (n- n (nlit 1)))})))))

;; ============================================================
;; Int
;; ============================================================

;; ── Int literals ─────────────────────────────────────────────────────────────────────
;; `reify-term` used to recognise a ground operand only via `e/lit-nat?`. An Int literal
;; is `Int.ofNat k` / `Int.negSucc k` — a CONSTRUCTOR application, never a `lit-nat` — so
;; every negative literal degraded to an opaque atom. `ground-int-val` now sees through
;; both constructors and `Int.negSucc k` reifies as the constant -(k+1), which promoted
;; five entries below from `gap` to `proves`.
;;
;; What is still missing is Int SCALAR MULTIPLICATION: folding `2 * x` over Int needs an
;; Int-level scale eval proof, and `mk-scale-eval-proof`'s bridge is built out of
;; Nat.mul_succ/Nat.mul_comm and is Nat-only. Same for `Neg.neg` applied to a literal.
(def ^:private int-mul-gap
  "Int scalar multiplication / literal negation needs an Int-level scale eval proof;
   mk-scale-eval-proof's Nat.mul_succ/Nat.mul_comm bridge is Nat-only")

(deftest corpus-int-linear
  (testing "lean4 omega.lean — Int linear fragment"
    ;; L6 / L8
    (proves "(1:Int) < 0 → False"
            (ex [] (fn [] {:hyps [(i< (ilit 1) (ilit 0))] :concl FALSE})))
    (proves "(0:Int) < 0 → False"
            (ex [] (fn [] {:hyps [(i< (ilit 0) (ilit 0))] :concl FALSE})))
    ;; L95 / L97 / L119
    (proves "(7:Int) = 0 → False"
            (ex [] (fn [] {:hyps [(i= (ilit 7) (ilit 0))] :concl FALSE})))
    (proves "(7:Int) ≤ 0 → False"
            (ex [] (fn [] {:hyps [(i<= (ilit 7) (ilit 0))] :concl FALSE})))
    (proves "(7:Int) < 0 → False"
            (ex [] (fn [] {:hyps [(i< (ilit 7) (ilit 0))] :concl FALSE})))
    ;; L12
    (proves "0 ≤ x → x ≤ -1 → False"
            (ex [["x" INT]] (fn [x] {:hyps [(i<= (ilit 0) x) (i<= x (ilit -1))] :concl FALSE})))
    ;; L106 / L108 — ground Int subtraction
    (proves "(7:Int) - 14 = 0 → False"
            (ex [] (fn [] {:hyps [(i= (i- (ilit 7) (ilit 14)) (ilit 0))] :concl FALSE})))
    (proves "(14:Int) - 7 ≤ 0 → False"
            (ex [] (fn [] {:hyps [(i<= (i- (ilit 14) (ilit 7)) (ilit 0))] :concl FALSE})))
    ;; L113 / L115 — Neg.neg
    (gap "-(7:Int) = 0 → False" int-mul-gap
         (ex [] (fn [] {:hyps [(i= (ineg (ilit 7)) (ilit 0))] :concl FALSE})))
    (gap "-(-7:Int) ≤ 0 → False" int-mul-gap
         (ex [] (fn [] {:hyps [(i<= (ineg (ilit -7)) (ilit 0))] :concl FALSE})))
    ;; L121 — gcd tightening (2 ∤ 1), reached without any Int literal folding
    (proves "x + x + 1 = 0 → False"
            (ex [["x" INT]] (fn [x] {:hyps [(i= (i+ (i+ x x) (ilit 1)) (ilit 0))] :concl FALSE})))
    ;; L123
    (gap "2*x + 1 = 0 → False" int-mul-gap
         (ex [["x" INT]] (fn [x] {:hyps [(i= (i+ (i* (ilit 2) x) (ilit 1)) (ilit 0))]
                                  :concl FALSE})))
    ;; L125 / L127
    (proves "x + x + y + y + 1 = 0 → False"
            (ex [["x" INT] ["y" INT]]
                (fn [x y] {:hyps [(i= (i+ (i+ (i+ (i+ x x) y) y) (ilit 1)) (ilit 0))] :concl FALSE})))
    ;; L129
    (proves "0 ≤ -7 + x → 0 ≤ 3 - x → False"
            (ex [["x" INT]]
                (fn [x] {:hyps [(i<= (ilit 0) (i+ (ilit -7) x))
                                (i<= (ilit 0) (i- (ilit 3) x))]
                         :concl FALSE})))
    ;; L133 / L135
    (gap "0 ≤ 2*x + 1 → 2*x + 1 ≤ 0 → False" int-mul-gap
         (ex [["x" INT]]
             (fn [x] {:hyps [(i<= (ilit 0) (i+ (i* (ilit 2) x) (ilit 1)))
                             (i<= (i+ (i* (ilit 2) x) (ilit 1)) (ilit 0))]
                      :concl FALSE})))
    ;; L137 — equality hypothesis chaining
    (gap "0 ≤ 2*x+1 → x = y → 2*y+1 ≤ 0 → False" int-mul-gap
         (ex [["x" INT] ["y" INT]]
             (fn [x y] {:hyps [(i<= (ilit 0) (i+ (i* (ilit 2) x) (ilit 1)))
                               (i= x y)
                               (i<= (i+ (i* (ilit 2) y) (ilit 1)) (ilit 0))]
                        :concl FALSE})))
    ;; L145
    (gap "1 ≤ -3*x → 1 ≤ 2*x → False" int-mul-gap
         (ex [["x" INT]]
             (fn [x] {:hyps [(i<= (ilit 1) (i* (ilit -3) x))
                             (i<= (ilit 1) (i* (ilit 2) x))]
                      :concl FALSE})))
    ;; L205
    (proves "a < b → b < a → False"
            (ex [["a" INT] ["b" INT]] (fn [a b] {:hyps [(i< a b) (i< b a)] :concl FALSE})))
    ;; L234
    (proves "b + 2 > 3 + b → False"
            (ex [["b" INT]]
                (fn [b] {:hyps [(i< (i+ (ilit 3) b) (i+ b (ilit 2)))] :concl FALSE})))
    ;; L246
    (proves "a > 0 → b > 5 → c < -10 → a + b - c < 3 → False"
            (ex [["a" INT] ["b" INT] ["c" INT]]
                (fn [a b c] {:hyps [(i< (ilit 0) a) (i< (ilit 5) b) (i< c (ilit -10))
                                    (i< (i- (i+ a b) c) (ilit 3))]
                             :concl FALSE})))
    ;; L249 — double negation of an order fact
    (proves "b > 0 → ¬(b ≥ 0) → False"
            (ex [["b" INT]]
                (fn [b] {:hyps [(i< (ilit 0) b) (p-not (i<= (ilit 0) b))] :concl FALSE})))
    ;; L335
    (proves "x < y → ¬¬(y < x) → False"
            (ex [["x" INT] ["y" INT]]
                (fn [x y] {:hyps [(i< x y) (p-not (p-not (i< y x)))] :concl FALSE})))
    ;; L174 — conjunction in a hypothesis
    (proves "(x > 0 ∧ x < -1) → False"
            (ex [["x" INT]]
                (fn [x] {:hyps [(p-and (i< (ilit 0) x) (i< x (ilit -1)))] :concl FALSE})))
    ;; L213 — the product A*B is atomised, then scaled
    (gap "0 < A*B → 0 < 8*(A*B)" int-mul-gap
         (ex [["A" INT] ["B" INT]]
             (fn [A B] {:hyps [(i< (ilit 0) (i* A B))]
                        :concl (i< (ilit 0) (i* (ilit 8) (i* A B)))})))
    ;; L265
    (gap "0 ≤ a → 0*0 ≤ 2*a" int-mul-gap
         (ex [["a" INT]]
             (fn [a] {:hyps [(i<= (ilit 0) a)]
                      :concl (i<= (i* (ilit 0) (ilit 0)) (i* (ilit 2) a))})))
    ;; L207 — an Int EQUALITY goal; by_contra needs the ≠ → disjunction lemma
    ;; (Int.lt_or_gt_of_ne)
    (proves "v0 + v1 + c = 10 → v0 + 5 + (v1 - 3) + (c - 2) = 10"
            (ex [["v0" INT] ["v1" INT] ["c" INT]]
                (fn [v0 v1 c]
                  {:hyps [(i= (i+ (i+ v0 v1) c) (ilit 10))]
                   :concl (i= (i+ (i+ (i+ v0 (ilit 5)) (i- v1 (ilit 3))) (i- c (ilit 2)))
                              (ilit 10))})))
    ;; L84 — mixed Nat/Int
    (proves "0 < x → x + ↑y ≤ 0 → False"
            (ex [["x" INT] ["y" NAT]]
                (fn [x y] {:hyps [(i< (ilit 0) x)
                                  (i<= (i+ x (e/app (c "Int.ofNat") y)) (ilit 0))]
                           :concl FALSE})))))

(deftest corpus-int-goals
  (testing "lean4 omega.lean — Int goals (not just False)"
    ;; L175 — disjunctive goal
    (proves "x > 7 → x < 0 ∨ x > 3"
            (ex [["x" INT]]
                (fn [x] {:hyps [(i< (ilit 7) x)]
                         :concl (p-or (i< x (ilit 0)) (i< (ilit 3) x))})))
    ;; L329 — implication goal (introduced by `ex` as a hypothesis)
    (proves "a > 0 → a > -1"
            (ex [["a" INT]] (fn [a] {:hyps [(i< (ilit 0) a)] :concl (i< (ilit -1) a)})))
    ;; L332
    (proves "x + 1 ≤ y → ¬(y + 1 ≤ x)"
            (ex [["x" INT] ["y" INT]]
                (fn [x y] {:hyps [(i<= (i+ x (ilit 1)) y)]
                           :concl (p-not (i<= (i+ y (ilit 1)) x))})))
    ;; L226 — conjunction goal. Negating it needs ¬(P∧Q) → ¬P ∨ ¬Q, which Lean core
    ;; spells `Classical.not_and_iff_not_or_not` (`not_and_or` is the Mathlib name and
    ;; resolves nowhere).
    (proves "a ≤ b → b ≤ a → a ≤ b ∧ b ≤ a"
            (ex [["a" INT] ["b" INT]]
                (fn [a b] {:hyps [(i<= a b) (i<= b a)] :concl (p-and (i<= a b) (i<= b a))})))
    ;; L267 / L269 — `≠` goal
    (proves "x < y → x ≠ y"
            (ex [["x" INT] ["y" INT]] (fn [x y] {:hyps [(i< x y)] :concl (i-ne x y)})))
    ;; L186 — 5×5 dense Int system
    (gap "5-variable dense Int system ⊢ e = 3"
         "Int equality GOAL needs Int.lt_or_gt_of_ne (absent from init-medium); the
          hypotheses also hit the Int literal gap"
         (ex [["a" INT] ["b" INT] ["c" INT] ["d" INT] ["e" INT]]
             (fn [a b c d e]
               (let [s (fn [& xs] (reduce i+ xs))]
                 {:hyps [(i= (s (i* (ilit 2) a) b c d e) (ilit 4))
                         (i= (s a (i* (ilit 2) b) c d e) (ilit 5))
                         (i= (s a b (i* (ilit 2) c) d e) (ilit 6))
                         (i= (s a b c (i* (ilit 2) d) e) (ilit 7))
                         (i= (s a b c d (i* (ilit 2) e)) (ilit 8))]
                  :concl (i= e (ilit 3))}))))))

(def ^:private int-div-gap
  "Int division bounds are EMITTED and kernel-checkable now — `Int.mul_ediv_self_le`
   and `Int.lt_mul_ediv_self_add` are in the bundled store and `add-div-bounds` states
   both over the goal's own divisor spelling (see int-div-bounds-are-emitted below).
   They are still useless to the solver, for the same reason as `int-mul-gap`: the
   bounds are stated as `k * (x / k)`, and Int scalar multiplication reifies as a fresh
   opaque atom `z` instead of `k · q`, so what reaches the solver is `0 ≤ x - z ≤ k-1`
   — true, certified, and saying nothing about `q`. Unblocking these needs an Int-level
   scale eval proof, not a lemma.")

(deftest corpus-int-div
  (testing "lean4 omega.lean — Int division"
    ;; L222
    (gap "ε > 0 → ε / 2 < ε" int-div-gap
         (ex [["e" INT]] (fn [ee] {:hyps [(i< (ilit 0) ee)]
                                   :concl (i< (idiv ee (ilit 2)) ee)})))
    ;; L17
    (gap "2 * (x / 2) > x → False" int-div-gap
         (ex [["x" INT]] (fn [x] {:hyps [(i< x (i* (ilit 2) (idiv x (ilit 2))))]
                                  :concl FALSE})))
    ;; L15
    (gap "x % 2 > 5 → False"
         "the Int emod decomposition still needs the Int.emod_def cast bridge, and rides
          on the Int div bounds"
         (ex [["x" INT]] (fn [x] {:hyps [(i< (ilit 5) (imod x (ilit 2)))] :concl FALSE})))
    ;; L293 — a quotient by a SYMBOLIC divisor is a plain atom; no bounds needed
    (proves "32 / a < b → b < c → 32 / a < c"
            (ex [["a" INT] ["b" INT] ["c" INT]]
                (fn [a b c] {:hyps [(i< (idiv (ilit 32) a) b) (i< b c)]
                             :concl (i< (idiv (ilit 32) a) c)})))))

(deftest int-div-bounds-are-emitted
  (testing "add-div-bounds' Int branch runs and produces certified facts"
    ;; The Int branch spent two releases inert, first because `Int.mul_ediv_self_le` /
    ;; `Int.lt_mul_ediv_self_add` were missing from the store, then because it read the
    ;; divisor with `e/lit-nat-val` — which is nil for `Int.ofNat 2` — and threw straight
    ;; into a bare `catch`. Both failures looked identical from outside: a quotient
    ;; reaching the solver unconstrained. `*strict-div-bounds*` makes them visible.
    (let [v (ns-resolve 'ansatz.tactic.omega-proof 'add-div-bounds)
          orig @v
          deltas (atom [])
          example (ex [["e" INT]] (fn [ee] {:hyps [(i< (ilit 0) ee)]
                                            :concl (i< (idiv ee (ilit 2)) ee)}))]
      (with-redefs-fn {v (fn [st table problem]
                           (let [[t p] (orig st table problem)]
                             (swap! deltas conj
                                    [(count (:div-atoms table))
                                     (- (count (:constraints p))
                                        (count (:constraints problem)))])
                             [t p]))}
        (fn []
          (binding [omega-proof/*strict-div-bounds* true]
            ;; NOT `:ok` — the goal is still undecided (see int-div-gap). The point is
            ;; that stating the bounds neither throws nor silently no-ops.
            (is (not= :ok (run-omega example))
                "still blocked on Int scalar multiplication, not on a missing lemma"))))
      (is (= [1] (distinct (map first @deltas)))
          "the Int quotient must be tagged as a div atom")
      (is (pos? (reduce + (map second @deltas)))
          (str "add-div-bounds must ADD constraints for the Int quotient. Zero means the "
               "branch threw into its `catch` again — run with *strict-div-bounds* true "
               "to see why. Saw: " (pr-str @deltas))))))

;; ============================================================
;; Negative tests — lean4's `fail_if_success omega`
;; ============================================================

;; ============================================================
;; Logical connectives — the propositional plumbing around the arithmetic
;; ============================================================

(deftest corpus-connectives
  (testing "∧ / → / ↔ in both hypothesis and goal position"
    ;; Each of these routes through one core lemma that omega used to name WRONGLY —
    ;; with a Mathlib spelling that resolves in no Lean core store. Every one of them
    ;; failed by omega quietly declining the goal, never by an error naming the constant.
    ;;
    ;;   ¬(P ∧ Q) → ¬P ∨ ¬Q     Classical.not_and_iff_not_or_not   (was `not_and_or`)
    ;;   ¬(P → Q) → P ∧ ¬Q      Classical.not_imp                  (was `not_imp`)
    ;;   (P ↔ Q) → …            Decidable.iff_iff_and_or_not_and_not
    ;;                                        (was `iff_iff_and_or_not_and_not`; the core
    ;;                                         lemma additionally takes a `[Decidable Q]`)
    ;;   ¬(P ↔ Q) → (¬P ↔ Q)    Decidable.not_iff — present all along, but applied with
    ;;                          its instance on the wrong proposition, which only became
    ;;                          reachable once the store carried the lemma at all.

    ;; ¬(P ∧ Q): conjunction GOAL, over Nat as well as the Int entry at L226 above
    (proves "a ≤ b → b ≤ a → a ≤ b ∧ b ≤ a  (Nat)"
            (ex [["a" NAT] ["b" NAT]]
                (fn [a b] {:hyps [(n<= a b) (n<= b a)] :concl (p-and (n<= a b) (n<= b a))})))

    ;; ¬(P → Q): implication GOAL. `ex` would intro a leading hypothesis, so the
    ;; implication has to sit inside the conclusion to reach negate-goal-forall.
    (proves "x > 7 → ((x < 3) → (x < 1))"
            (ex [["x" NAT]]
                (fn [x] {:hyps [(n< (nlit 7) x)]
                         :concl (p-imp (n< x (nlit 3)) (n< x (nlit 1)))})))
    (proves "x > 7 → ((x < 3) → (x < 1))  (Int)"
            (ex [["x" INT]]
                (fn [x] {:hyps [(i< (ilit 7) x)]
                         :concl (p-imp (i< x (ilit 3)) (i< x (ilit 1)))})))

    ;; P → Q as a HYPOTHESIS: Decidable.not_or_of_imp, ¬P ∨ Q, then a disjunction split
    (proves "(x < 3 → y < 3) → x < 1 → y > 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(p-imp (n< x (nlit 3)) (n< y (nlit 3)))
                                  (n< x (nlit 1)) (n< (nlit 5) y)]
                           :concl FALSE})))

    ;; P ↔ Q as a HYPOTHESIS: (P∧Q) ∨ (¬P∧¬Q), then a disjunction split. Both branches
    ;; must refute, so this really does traverse the Iff expansion.
    (proves "(x < 3 ↔ y < 3) → x < 1 → y > 5 → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(p-iff (n< x (nlit 3)) (n< y (nlit 3)))
                                  (n< x (nlit 1)) (n< (nlit 5) y)]
                           :concl FALSE})))

    ;; P ↔ Q as a GOAL: ¬(P ↔ Q) → (¬P ↔ Q) via Decidable.not_iff, then the Iff
    ;; expansion above. Applying that lemma's `[Decidable b]` to P rather than Q made
    ;; the kernel reject the term outright.
    (proves "x = y → (x < 3 ↔ y < 3)"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(n= x y)] :concl (p-iff (n< x (nlit 3)) (n< y (nlit 3)))})))
    (proves "x = y → (x < 3 ↔ y < 3)  (Int)"
            (ex [["x" INT] ["y" INT]]
                (fn [x y] {:hyps [(i= x y)] :concl (p-iff (i< x (ilit 3)) (i< y (ilit 3)))})))))

(deftest corpus-negative
  (testing "lean4 omega.lean — goals omega must REFUSE"
    ;; L1 — lean4's omega REFUSES a goal with no arithmetic content. Ours tries
    ;; `decide` first (ansatz.tactic.omega:914), which closes `True` outright. Harmless
    ;; — omega proving a true, decidable goal is not unsoundness — but it is a real
    ;; behavioural difference, recorded rather than asserted either way.
    (divergence "True (no usable constraints)"
                "our omega tries `decide` before reifying, so it closes decidable ground goals"
                (ex [] (fn [] {:hyps [] :concl TRUE})))
    ;; L532
    (rejects "0 < 0"
             (ex [] (fn [] {:hyps [] :concl (n< (nlit 0) (nlit 0))})))
    ;; L542
    (rejects "(x : Nat) ⊢ x < 0"
             (ex [["x" NAT]] (fn [x] {:hyps [] :concl (n< x (nlit 0))})))
    ;; L9
    (rejects "(0:Int) < 1 ⊢ False"
             (ex [] (fn [] {:hyps [(i< (ilit 0) (ilit 1))] :concl FALSE})))
    ;; L11
    (rejects "0 ≤ x → x ≤ 1 ⊢ False"
             (ex [["x" INT]] (fn [x] {:hyps [(i<= (ilit 0) x) (i<= x (ilit 1))] :concl FALSE})))
    ;; L43 — 6x + 7y = 5 HAS integer solutions over Int (x = 2, y = -1)
    (rejects "(Int) 6*x + 7*y = 5 ⊢ False"
             (ex [["x" INT] ["y" INT]]
                 (fn [x y] {:hyps [(i= (i+ (i* (ilit 6) x) (i* (ilit 7) y)) (ilit 5))]
                            :concl FALSE})))
    ;; L611
    (rejects "x < y + z (three unconstrained Nats)"
             (ex [["x" NAT] ["y" NAT] ["z" NAT]]
                 (fn [x y z] {:hyps [] :concl (n< x (n+ y z))})))
    ;; L654
    (rejects "b + c + d + e < 100"
             (ex [["b" NAT] ["c" NAT] ["d" NAT] ["e" NAT]]
                 (fn [b c d e] {:hyps [] :concl (n< (n+ (n+ (n+ b c) d) e) (nlit 100))})))
    ;; a FALSE div fact must not be provable
    (rejects "a / 3 * 3 = a"
             (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n= (n* (ndiv a (nlit 3)) (nlit 3)) a)})))
    (rejects "a % 3 = 0"
             (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n= (nmod a (nlit 3)) (nlit 0))})))
    (rejects "a < a / 3 * 3"
             (ex [["a" NAT]] (fn [a] {:hyps [] :concl (n< a (n* (ndiv a (nlit 3)) (nlit 3)))})))))

;; ============================================================
;; min / max  (lean4 Frontend.lean:211-220, OmegaM.lean:226-229)
;; ============================================================
;;
;; Neither omega implementation used to handle `Min.min`/`Max.max` at all — they
;; reached the solver as opaque atoms, so `n ≤ max n m` was unprovable. lean4 either
;; rewrites through `Int.min_def`/`Int.max_def` (splitMinMax) or atomises with the
;; one-sided `min_le_left`/`le_max_left` facts. We take the splitting route: the atom
;; is tied down by the disjunction (a ≤ b ∧ m = a) ∨ (¬(a ≤ b) ∧ m = b), proved from
;; `Decidable.em` + `if_pos`/`if_neg` on the instance's own `ite`. That is complete,
;; so the one-sided bounds fall out of it too.
;;
;; NOTE on instances: the bundled slice exports `instMinNat` and `Int.instMin` /
;; `Int.instMax`, but NOT `instMaxNat`. Nat `max` is therefore spelled with the bare
;; `maxOfLe` instance below — which doubles as a check that we read the LE and
;; Decidable arguments off whatever instance we are handed rather than hard-coding
;; `Nat.decLe`.

(def ^:private nat-max-inst
  (e/app* (e/const' (name/from-string "maxOfLe") [lvl/zero])
          NAT (c "instLENat") (c "Nat.decLe")))
(defn- nmax' [a b] (e/app* (c1 "Max.max") NAT nat-max-inst a b))

(deftest corpus-minmax
  (testing "min/max over Nat"
    (proves "min a b ≤ a"
            (ex [["a" NAT] ["b" NAT]] (fn [a b] {:hyps [] :concl (n<= (nmin a b) a)})))
    (proves "min a b ≤ b"
            (ex [["a" NAT] ["b" NAT]] (fn [a b] {:hyps [] :concl (n<= (nmin a b) b)})))
    (proves "a ≤ max a b"
            (ex [["a" NAT] ["b" NAT]] (fn [a b] {:hyps [] :concl (n<= a (nmax' a b))})))
    (proves "b ≤ max a b"
            (ex [["a" NAT] ["b" NAT]] (fn [a b] {:hyps [] :concl (n<= b (nmax' a b))})))
    ;; needs the SPLIT, not just the one-sided bounds
    (proves "min a b + max a b = a + b"
            (ex [["a" NAT] ["b" NAT]]
                (fn [a b] {:hyps [] :concl (n= (n+ (nmin a b) (nmax' a b)) (n+ a b))})))
    (proves "a ≤ b → min a b = a"
            (ex [["a" NAT] ["b" NAT]]
                (fn [a b] {:hyps [(n<= a b)] :concl (n= (nmin a b) a)})))
    (proves "a ≤ b → max a b = b"
            (ex [["a" NAT] ["b" NAT]]
                (fn [a b] {:hyps [(n<= a b)] :concl (n= (nmax' a b) b)})))
    ;; the downstream shape this was added for: clamping a retarget / quorum bound
    ;; (stated as two goals rather than one conjunction: negating a conjunctive GOAL
    ;; needs `not_and_or`, which the bundled slice does not carry — see
    ;; ansatz.tactic.omega-constants-test)
    (proves "1 ≤ max n 1"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n<= (nlit 1) (nmax' n (nlit 1)))})))
    (proves "n ≤ max n 1"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n<= n (nmax' n (nlit 1)))})))
    (proves "min n 100 ≤ 100"
            (ex [["n" NAT]] (fn [n] {:hyps [] :concl (n<= (nmin n (nlit 100)) (nlit 100))})))
    ;; ground min/max folds through the same split
    (proves "min 3 7 = 3"
            (ex [] (fn [] {:hyps [] :concl (n= (nmin (nlit 3) (nlit 7)) (nlit 3))})))
    (proves "max 3 7 = 7"
            (ex [] (fn [] {:hyps [] :concl (n= (nmax' (nlit 3) (nlit 7)) (nlit 7))}))))
  (testing "min/max over Int"
    (proves "min a b ≤ a  (Int)"
            (ex [["a" INT] ["b" INT]] (fn [a b] {:hyps [] :concl (i<= (imin a b) a)})))
    (proves "b ≤ max a b  (Int)"
            (ex [["a" INT] ["b" INT]] (fn [a b] {:hyps [] :concl (i<= b (imax a b))})))
    (proves "a ≤ c → b ≤ c → max a b ≤ c  (Int)"
            (ex [["a" INT] ["b" INT] ["c" INT]]
                (fn [a b c] {:hyps [(i<= a c) (i<= b c)] :concl (i<= (imax a b) c)}))))
  (testing "min/max facts that are FALSE must still be refused"
    (rejects "min a b = a"
             (ex [["a" NAT] ["b" NAT]] (fn [a b] {:hyps [] :concl (n= (nmin a b) a)})))
    (rejects "a ≤ min a b"
             (ex [["a" NAT] ["b" NAT]] (fn [a b] {:hyps [] :concl (n<= a (nmin a b))})))))

;; ============================================================
;; The Bool → Prop bridge
;; ============================================================
;;
;; `grind`/`simp` case-split a `Nat.ble`/`Nat.blt` discriminant through `Bool.rec` and
;; hand omega a BOOLEAN equation. lean4's own `addFact` drops these (its `Eq α x y`
;; match has no `Bool` case — Frontend.lean:441-448); its omega only ever sees them
;; because a `simp` pre-pass has already rewritten `Nat.ble a b = true` to `a ≤ b`.
;; We do that rewrite inside the reifier instead, with an explicit proof term.
;;
;; This is the ONLY thing the ~440 lines of hand-rolled proof-shape fallbacks that
;; used to sit in ansatz.tactic.omega were still doing: with them spliced out, the
;; whole suite lost exactly three tests, all insertion-sort proofs with the goal shape
;; `hc : Nat.ble x y = false ⊢ y ≤ x`.

(deftest corpus-bool-bridge
  (testing "Nat.ble"
    (proves "Nat.ble x y = true → x ≤ y"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(b= (ble x y) BTRUE)] :concl (n<= x y)})))
    ;; THE isort shape: Bool.rec's false branch, goal with the operands swapped
    (proves "Nat.ble x y = false → y ≤ x"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(b= (ble x y) BFALSE)] :concl (n<= y x)})))
    (proves "Nat.ble x y = false → y < x"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(b= (ble x y) BFALSE)] :concl (n< y x)})))
    ;; (`ble x y = true` and `ble y x = false` are CONSISTENT — both hold when x < y;
    ;; the contradiction needs the strict comparison on one side)
    (proves "Nat.ble x y = true → Nat.blt y x = true → False"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(b= (ble x y) BTRUE) (b= (blt y x) BTRUE)] :concl FALSE})))
    ;; combined with ordinary arithmetic facts
    (proves "Nat.ble x y = false → x ≤ z → y < z + 1"
            (ex [["x" NAT] ["y" NAT] ["z" NAT]]
                (fn [x y z] {:hyps [(b= (ble x y) BFALSE) (n<= x z)]
                             :concl (n< y (n+ z (nlit 1)))}))))
  (testing "Nat.blt"
    (proves "Nat.blt x y = true → x < y"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(b= (blt x y) BTRUE)] :concl (n< x y)})))
    (proves "Nat.blt x y = false → y ≤ x"
            (ex [["x" NAT] ["y" NAT]]
                (fn [x y] {:hyps [(b= (blt x y) BFALSE)] :concl (n<= y x)}))))
  (testing "the bridge must not manufacture facts"
    (rejects "Nat.ble x y = true → y ≤ x"
             (ex [["x" NAT] ["y" NAT]]
                 (fn [x y] {:hyps [(b= (ble x y) BTRUE)] :concl (n<= y x)})))
    (rejects "Nat.ble x y = false → x ≤ y"
             (ex [["x" NAT] ["y" NAT]]
                 (fn [x y] {:hyps [(b= (ble x y) BFALSE)] :concl (n<= x y)})))))

;; ============================================================
;; Int literals
;; ============================================================
;;
;; `Int.negSucc k` is the only spelling a negative Int literal has, and it is a
;; CONSTRUCTOR application — never an `e/lit-nat?` — so it used to reach the solver as
;; an opaque atom. `ground-int-val` now sees through both `Int.ofNat` and `Int.negSucc`.

(deftest corpus-int-literals
  (testing "negative literals are constants, not atoms"
    (proves "(-1 : Int) < 0"
            (ex [] (fn [] {:hyps [] :concl (i< (ilit -1) (ilit 0))})))
    (proves "(-5 : Int) ≤ -3"
            (ex [] (fn [] {:hyps [] :concl (i<= (ilit -5) (ilit -3))})))
    (proves "x ≤ -3 → x ≤ -1"
            (ex [["x" INT]] (fn [x] {:hyps [(i<= x (ilit -3))] :concl (i<= x (ilit -1))})))
    ;; (an Int EQUALITY goal would need `Int.lt_or_gt_of_ne`, absent from the bundled
    ;; slice — see ansatz.tactic.omega-constants-test; the inequality says as much here)
    (proves "-4 ≤ x → x ≤ -4 → 0 ≤ x + 4"
            (ex [["x" INT]]
                (fn [x] {:hyps [(i<= (ilit -4) x) (i<= x (ilit -4))]
                         :concl (i<= (ilit 0) (i+ x (ilit 4)))})))
    (proves "0 ≤ x + (-3) → 3 ≤ x"
            (ex [["x" INT]]
                (fn [x] {:hyps [(i<= (ilit 0) (i+ x (ilit -3)))] :concl (i<= (ilit 3) x)})))
    (rejects "x ≤ -3 → -1 ≤ x"
             (ex [["x" INT]] (fn [x] {:hyps [(i<= x (ilit -3))] :concl (i<= (ilit -1) x)})))))
