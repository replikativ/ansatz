(ns ansatz.memory-model-probe-test
  "Acceptance tests from the spindel memory-model probe (2026-10-26).

  Definitions: an ownership model where closing a scope drops the scope and every row it
  owns; `inv` = every row's owner is an open scope. Every theorem here is accepted by Lean 4
  (see test/lean/memory_model_probe.lean, checked with lean_run_code). Each test states the
  same theorem in ansatz surface syntax with the proof script that mirrors the Lean one.
  At 3628bad decide (Init registry carried the scoped `Classical.propDecidable`), induction
  (no generalization of dependent hypotheses), simp_all (single round; conditional hypothesis
  rewrites crashed) and grind (re-split the same condition without bound) failed them.

  Surface-syntax notes: `->` is clojure.core's threading macro, so implications are written
  `=>`, `→` or `arrow` (all n-ary)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]))

(def ^:private model
  '[(ansatz.core/structure Own [] (ent Nat) (scope Nat))
    (ansatz.core/structure St [] (open (List Nat)) (owns (List Own)))

    (ansatz.core/defn memq [x :- Nat, xs :- (List Nat)] Bool
      (match xs [nil false] [(cons h t) (if (Nat.beq x h) true (memq x t))]))

    (ansatz.core/defn owners-open [os :- (List Own), op :- (List Nat)] Bool
      (match os [nil true] [(cons o t) (if (memq (:scope o) op) (owners-open t op) false)]))

    (ansatz.core/defn inv [s :- St] Bool (owners-open (:owns s) (:open s)))

    (ansatz.core/defn drop-owned [sc :- Nat, os :- (List Own)] (List Own)
      (match os [nil (List.nil Own)]
             [(cons o t) (if (Nat.beq (:scope o) sc) (drop-owned sc t) (List.cons Own o (drop-owned sc t)))]))

    (ansatz.core/defn drop-nat [x :- Nat, xs :- (List Nat)] (List Nat)
      (match xs [nil (List.nil Nat)]
             [(cons h t) (if (Nat.beq h x) (drop-nat x t) (List.cons Nat h (drop-nat x t)))]))

    (ansatz.core/defn close [sc :- Nat, s :- St] St
      (St.mk (drop-nat sc (:open s)) (drop-owned sc (:owns s))))])

;; Each test starts from Init + the model: other namespaces' fixtures replace the global env,
;; so the model cannot be defined at load time. Theorems a test builds on are proved inside
;; that same test, in order.
(use-fixtures :each
  (fn [f]
    (a/load-init!)
    (binding [a/*verbose* false
              *ns* (the-ns 'ansatz.memory-model-probe-test)]
      (run! eval model)
      (f))))

(defmacro ^:private accepted?
  "Run a theorem form; true if ansatz accepts it within timeout-ms, else report and false."
  [timeout-ms form]
  `(let [f# (future (try ~form :ok (catch Throwable t# t#)))
         r# (deref f# ~timeout-ms ::timeout)]
     (when (= ::timeout r#) (future-cancel f#))
     (cond (= :ok r#) true
           (= ::timeout r#) (do (println "TIMEOUT after" ~timeout-ms "ms:" '~(second form)) false)
           :else (do (println "REJECTED" '~(second form) "-" (.getMessage ^Throwable r#)) false))))

(deftest t0-executable-model
  (testing "compiled definitions run as Clojure"
    (let [inv @(resolve 'inv) close @(resolve 'close) st @(resolve '->St) own @(resolve '->Own)]
      (is (true? (inv (st '(1 2) (list (own 7 1) (own 8 2))))))
      (is (true? (inv (close 2 (st '(1 2) (list (own 7 1) (own 8 2)))))))
      (is (false? (inv (st '(1) (list (own 8 2)))))))))

(deftest t1-closed-instance
  (testing "control: rfl proves the closed instance (works today)"
    (is (accepted? 30000
                   (a/theorem conc-rfl [] (= (inv (close 2 (St.mk (List.cons Nat 1 (List.cons Nat 2 (List.nil Nat)))
                                                                  (List.cons Own (Own.mk 7 1) (List.cons Own (Own.mk 8 2) (List.nil Own))))))
                                             true)
                              (rfl)))))
  (testing "decide must prove the same closed, decidable proposition (Lean: by decide)"
    (is (accepted? 30000
                   (a/theorem conc-decide [] (= (inv (close 2 (St.mk (List.cons Nat 1 (List.cons Nat 2 (List.nil Nat)))
                                                                     (List.cons Own (Own.mk 7 1) (List.cons Own (Own.mk 8 2) (List.nil Own))))))
                                                true)
                              (decide))))))

(deftest t3-intros-arrow
  (testing "intros introduces both antecedents of a nested arrow"
    (is (accepted? 30000
                   (a/theorem intro-arrow [p :- Bool, q :- Bool]
                              (arrow (= p true) (arrow (= q true) (= p true)))
                              (intros) (assumption))))))

(deftest t4-unfolding
  (testing "control: the nil case closes by rfl"
    (is (accepted? 30000
                   (a/theorem nil-rfl [sc :- Nat, op :- (List Nat)]
                              (= (owners-open (drop-owned sc (List.nil Own)) (drop-nat sc op)) true)
                              (rfl)))))
  (testing "grind must close it by unfolding the hinted definitions"
    (is (accepted? 60000
                   (a/theorem nil-grind [sc :- Nat, op :- (List Nat)]
                              (= (owners-open (drop-owned sc (List.nil Own)) (drop-nat sc op)) true)
                              (grind "owners-open" "drop-owned"))))))

;; T5–T7 build on each other (memq-drop is a hint to the later ones), so one test proves them
;; in order.
(deftest t5-t7-grind
  (testing "T5, the 3-line lemma (Lean: induction op <;> grind [memq, dropNat, Nat.beq_eq])"
    (is (accepted? 60000
                   (a/theorem memq-drop [x :- Nat, sc :- Nat, op :- (List Nat)]
                              (arrow (= (memq x op) true) (arrow (= (Nat.beq x sc) false) (= (memq x (drop-nat sc op)) true)))
                              (induction op) (all_goals (intros)) (all_goals (grind "memq" "drop-nat"))))))
  (testing "T6, preservation, implication form (Lean: induction os <;> grind [...])"
    (is (accepted? 60000
                   (a/theorem close-pres [sc :- Nat, op :- (List Nat), os :- (List Own)]
                              (arrow (= (owners-open os op) true)
                                     (= (owners-open (drop-owned sc os) (drop-nat sc op)) true))
                              (induction os) (all_goals (intros))
                              (all_goals (grind "owners-open" "drop-owned" "drop-nat" "memq" "memq-drop"))))))
  (testing "T7, h depends on os: induction must revert/re-introduce it so the IH is usable"
    (is (accepted? 60000
                   (a/theorem close-pres-hyp [sc :- Nat, op :- (List Nat), os :- (List Own),
                                              h :- (= (owners-open os op) true)]
                              (= (owners-open (drop-owned sc os) (drop-nat sc op)) true)
                              (induction os)
                              (all_goals (grind "owners-open" "drop-owned" "drop-nat" "memq" "memq-drop")))))))

;; ── The same theorems with Lean's MANUAL scripts (reference.lean `memq_drop`/`close_pres`):
;; `induction … with` alternatives run in constructor order (nil first), `cases h : e` is
;; `(cases h e)`, `<;>` is `and_then`, implications are `=>` (or `→`/`arrow`).
(deftest t5-t8-manual
  (testing "T5. Lean: induction op; nil => simp [memq]; cons => intro hm hne; cases … <;> cases … <;> simp_all [...]"
    (is (accepted? 60000
                   (a/theorem memq-drop-m [x :- Nat, sc :- Nat, op :- (List Nat)]
                              (=> (= (memq x op) true) (= (Nat.beq x sc) false) (= (memq x (drop-nat sc op)) true))
                              (induction op)
                              (simp [memq])
                              (intro hm) (intro hne)
                              (and_then (and_then (cases hh (Nat.beq head sc)) (cases hx (Nat.beq x head)))
                                        (simp_all [memq drop-nat Nat.beq_eq]))))))
  (testing "T6. Lean: induction os; nil => intro _; simp [...]; cons => intro h; cases … <;> cases … <;> simp_all [...]"
    (is (accepted? 60000
                   (a/theorem close-pres-m [sc :- Nat, op :- (List Nat), os :- (List Own)]
                              (=> (= (owners-open os op) true)
                                  (= (owners-open (drop-owned sc os) (drop-nat sc op)) true))
                              (induction os)
                              (intro h0) (simp [drop-owned owners-open])
                              (intro h)
                              (and_then (and_then (cases hm (memq (:scope head) op)) (cases hs (Nat.beq (:scope head) sc)))
                                        (simp_all [owners-open drop-owned memq-drop-m]))))))
  (testing "T7. h is a binder before induction: induction reverts and re-introduces it per case"
    (is (accepted? 60000
                   (a/theorem close-pres-hyp-m [sc :- Nat, op :- (List Nat), os :- (List Own),
                                                h :- (= (owners-open os op) true)]
                              (= (owners-open (drop-owned sc os) (drop-nat sc op)) true)
                              (induction os)
                              (simp [drop-owned owners-open])
                              (and_then (and_then (cases hm (memq (:scope head) op)) (cases hs (Nat.beq (:scope head) sc)))
                                        (simp_all [owners-open drop-owned memq-drop-m]))))))
  (testing "T8. Lean: inv_close := close_pres sc s.open_ s.owns (term proof via exact)"
    (is (accepted? 60000
                   (a/theorem inv-close [sc :- Nat, s :- St]
                              (=> (= (inv s) true) (= (inv (close sc s)) true))
                              (exact (close-pres-m sc (:open s) (:owns s))))))))
