(ns ansatz.tactic.simp.simp-theorems
  "Lean 4.36.0 Meta/Tactic/Simp/SimpTheorems.lean (unchanged since 4.33.1):
   Origin (decl name post inv), mkSimpEntryOfDeclToUnfold and unfoldEvenWithEqns."
  (:require [ansatz.eqns :as eqns]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.meta.rec-ext :as rec-ext]))

;; ── Origin ────────────────────────────────────────────────────────────────────────────────
;; SimpTheorems.lean:69-91 `Origin.decl (declName) (post := true) (inv := false)`. An extracted
;; rule map carries the same identity as `:name` (a kernel Name), `:post` and `:inv`; hypothesis
;; rules carry `:hyp-fvar-id` (Lean `.fvar`); proof-term rules carry neither (Lean `.stx`).

(defn- name-str [n]
  (cond (nil? n) nil
        (instance? ansatz.kernel.Name n) (name/->string n)
        :else (str n)))

(defn origin
  "A declaration origin {:decl name-str :post bool :inv bool} (Lean `Origin.decl`)."
  ([declaration] (origin declaration true false))
  ([declaration post inv]
   {:decl (name-str declaration) :post (boolean post) :inv (boolean inv)}))

(defn origin-key
  "What Lean's `BEq Origin` compares (SimpTheorems.lean:105-112): a declaration's name AND
   direction — `thm` and `←thm` differ (issue #4290) — but NOT its phase, so erasing `thm`
   erases both its pre and its post entry. `[:fvar id]` for a hypothesis."
  [o]
  (cond (:decl o) [(:decl o) (boolean (:inv o))]
        (:fvar o) [:fvar (:fvar o)]
        :else nil))

(defn origin-converse
  "Lean `Origin.converse` (SimpTheorems.lean:100-103): `thm` ↔ `←thm`; nil for non-declarations."
  [o]
  (when (:decl o) (update o :inv not)))

(defn pp-origin
  "Lean `ppOrigin` (SimpTheorems.lean:258-268): `↓ ← n`, `← n`, `↓ n`, `n`."
  [o]
  (if-let [n (:decl o)]
    (str (when-not (:post o true) "↓ ") (when (:inv o) "← ") n)
    (pr-str o)))

(defn rule-origin
  "The origin of an extracted simp rule map, or nil for an anonymous proof-term rule."
  [rule]
  (cond (:name rule) (origin (:name rule) (:post rule true) (:inv rule false))
        (:hyp-fvar-id rule) {:fvar (:hyp-fvar-id rule)}
        :else nil))

(defn rule-origin-key [rule] (some-> (rule-origin rule) origin-key))

;; ── Declarations to unfold ────────────────────────────────────────────────────────────────

(defn unfold-even-with-eqns [environment n]
  (or (rec-ext/has-smart-unfolding-decl environment n)
      (not (rec-ext/is-recursive-definition environment n))))

(defn mk-simp-entry-of-decl-to-unfold [environment n]
  (let [n (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
        ci (env/lookup environment n)]
    (if-not (and ci (.isDef ci))
      []
      (let [equations (eqns/get-eqns-for? environment n)
            size (count equations)
            entries (mapv (fn [i equation]
                            {:kind :thm :name equation
                             :priority (if (> size 100)
                                         (if (= (inc i) size) 0 1)
                                         (- 100 i))})
                          (range size) equations)]
        (cond-> entries
          (or (not (seq equations)) (unfold-even-with-eqns environment n))
          (conj {:kind :to-unfold :name n}))))))
