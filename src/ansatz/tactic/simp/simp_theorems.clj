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

(defn name-str [n]
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

;; ── Registration state: Lean SimpTheorems.lemmaNames / erased ────────────────────────────
;; A simp set's registrations as origin keys (origin-key): `:added`/`:removed` adjust the
;; registrations inherited through `:inherited?` (a predicate, so the inherited corpus is never
;; copied), and `:erased` is Lean's `erased`. Rule maps stay where they are; visibility is
;; `(not (contains? erased (rule-origin-key rule)))`, as Lean's `inErasedSet`.

(defn registered?
  "Lean `lemmaNames.contains k` (SimpTheorems.lean:668-669)."
  [{:keys [added removed inherited?]} k]
  (and (not (contains? removed k))
       (or (contains? added k) (boolean (and inherited? (inherited? k))))))

(defn erase-core
  "Lean `eraseCore` (SimpTheorems.lean:612-622) for one origin key: erased, no longer registered."
  [state k]
  (-> state (update :erased (fnil conj #{}) k) (update :added (fnil disj #{}) k)
      (update :removed (fnil conj #{}) k)))

(defn add-theorem
  "Lean `addSimpTheorem` (SimpTheorems.lean:643-652) on the registration state: erase the
   registered converse — in EITHER direction, despite the name `eraseFwdIfBwd` (:634-638) —
   then register the origin. It never un-erases the origin itself."
  [state o]
  (let [k (origin-key o)
        kc (some-> (origin-converse o) origin-key)
        state (if (and kc (registered? state kc)) (erase-core state kc) state)]
    (-> state (update :added (fnil conj #{}) k) (update :removed (fnil disj #{}) k))))

(defn unerase
  "Lean `uneraseSimpEntry` (SimpTheorems.lean:702-705): what `simp [thm]` does before adding."
  [state k]
  (update state :erased (fnil disj #{}) k))

(defn erase
  "Lean `SimpTheorems.erase` (SimpTheorems.lean:675-690) for a declaration `n` (a string):
   the forward origin when it is registered or `n` is a declaration to unfold (`unfold?`, with
   its registered equation theorems `unfold-thms`, which eraseCore also erases, :616-618);
   otherwise `←n` when that is registered; otherwise nothing changes and the result carries
   `:warning` (Lean's warning that `n` does not have the `[simp]` attribute, :689). Returns
   {:state :erased-unfold n-or-nil :warning bool}."
  [state n {:keys [unfold? unfold-thms] :or {unfold? (constantly false) unfold-thms (constantly nil)}}]
  (let [fwd [n false] bwd [n true]
        cascade (fn [st] (reduce #(erase-core %1 [(str %2) false]) st (unfold-thms n)))]
    (cond
      (or (registered? state fwd) (unfold? n) (some? (unfold-thms n)))
      {:state (cascade (erase-core state fwd)) :erased-unfold n}
      (registered? state bwd)
      {:state (cascade (erase-core state bwd)) :erased-unfold n}
      :else {:state state :warning true})))

;; ── A custom simp set's registrations (Lean register_simp_attr) ───────────────────────────

(defn set-member->entry
  "A stored simp-set member (a name string, or an origin map) as {:name :post :inv}."
  [member]
  (if (map? member)
    {:name (str (:name member)) :post (boolean (:post member true)) :inv (boolean (:inv member false))}
    {:name (str member) :post true :inv false}))

(defn replay-set
  "Lean's SimpExtension state for a custom simp set: its members, in registration order, each
   expanded the way the attribute registers it (`expand` entry → {:theorems [{:name :post :inv
   :prio}] :to-unfold [name] :simprocs [{:name :post}]}; Attr.lean:16-56) and every generated
   theorem replayed through addSimpTheorem (add-theorem: the registered converse is erased in
   either direction; nothing is un-erased). A repeated registration keeps its first slot and
   takes the new priority (DiscrTree.insertKeyValue replaces the equal entry in place).
   Returns {:entries [visible theorems] :erased :to-unfold :simprocs}."
  ([members] (replay-set members (fn [e] {:theorems [(assoc e :prio 1000)]})))
  ([members expand]
   (let [same (fn [a b] (= (dissoc a :prio) (dissoc b :prio)))
         {:keys [state entries to-unfold simprocs]}
         (reduce (fn [acc member]
                   (let [{:keys [theorems] new-unfold :to-unfold new-procs :simprocs}
                         (expand (set-member->entry member))]
                     (-> (reduce (fn [acc th]
                                   (-> acc
                                       (update :state add-theorem (origin (:name th) (:post th) (:inv th)))
                                       (update :entries (fn [es]
                                                          (if (some #(same % th) es)
                                                            (mapv #(if (same % th) th %) es)
                                                            (conj es th))))))
                                 acc theorems)
                         (update :to-unfold into new-unfold)
                         (update :simprocs into new-procs))))
                 {:state {:erased #{} :added #{} :removed #{}} :entries [] :to-unfold [] :simprocs []}
                 members)
         erased (:erased state)]
     {:entries (into [] (remove #(contains? erased [(:name %) (:inv %)])) entries)
      :erased erased
      :to-unfold (vec (distinct to-unfold))
      :simprocs (vec (distinct simprocs))})))

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

(defn attr-entries-of-decl
  "Lean Meta/Tactic/Simp/Attr.lean:16-34 addDeclToUnfold — what `attribute [s ↓] d` registers
   for a definition `d`: only the unfolding for a projection or reducible definition
   (`ignore-equations?`, Simp.ignoreEquations); otherwise each equation theorem with the
   attribute's phase and priority, plus the unfolding when unfoldEvenWithEqns; or the unfolding
   alone without equations."
  [environment n post prio ignore-equations?]
  (let [nm (if (instance? ansatz.kernel.Name n) n (name/from-string (str n)))
        equations (when-not (ignore-equations? nm) (eqns/get-eqns-for? environment nm))]
    (if (seq equations)
      {:theorems (mapv (fn [eq] {:name (name-str eq) :post (boolean post) :inv false :prio prio}) equations)
       :to-unfold (when (unfold-even-with-eqns environment nm) [(name-str nm)])}
      {:to-unfold [(name-str nm)]})))
