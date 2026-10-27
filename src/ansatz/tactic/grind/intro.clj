(ns ansatz.tactic.grind.intro
  "Eager existential elimination (Grind/Intro.lean applyCases? and assertAt)."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]
            [ansatz.tactic.proof :as proof]))

(defn candidate [branch]
  (some (fn [[p fact]]
          (let [[h args] (e/get-app-fn-args p)]
            (when (and (e/const? h) (= "Exists" (name/->string (e/const-name h)))
                       (not (contains? (:exists-seen branch) p)))
              (assoc fact :prop p :args args)))) (:facts branch)))

(defn eliminate [branch {:keys [prop proof args gen]} solve]
  (let [[alpha predicate] args
        [ps xid] (proof/alloc-id (:ps branch))
        [ps hid] (proof/alloc-id ps)
        x (e/fvar xid) h (e/fvar hid)
        ;; Cases reduces the predicate application in the introduced hypothesis.
        instance (if (e/lam? predicate) (e/instantiate1 (e/lam-body predicate) x)
                     (e/app predicate x))
        lctx (-> (:lctx (:tc branch)) (red/lctx-add-local xid "x" alpha)
                 (red/lctx-add-local hid "h" instance))
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) lctx)
        branch (-> branch (assoc :ps ps :tc st) (update :exists-seen conj prop)
                   (update :raw-facts conj {:prop instance :proof h :gen gen}))
        hfalse (solve branch)
        continuation (e/lam "x" alpha
                            (e/abstract1 (e/lam "h" instance (e/abstract1 hfalse hid) :default) xid) :default)
        sort (#'tc/cached-whnf st (tc/infer-type st alpha))
        false-expr (e/const' (name/from-string "False") [])]
    ;; The bundled Init exports casesOn rather than the convenience Exists.elim.
    (e/app* (e/const' (name/from-string "Exists.casesOn") [(e/sort-level sort)])
            alpha predicate (e/lam "h" prop false-expr :default) proof continuation)))
