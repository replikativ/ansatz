;; A provenance-semiring protocol — the discrete instance of a probabilistic-
;; effect algebra, shared by the relational search (ansatz.rel), the certified
;; optimizer (wandler), and (via an adapter) the datalog store (datahike).
;;
;; This namespace is deliberately PURE: no kernel, no engine, no wandler/datahike
;; dependency — so it can be lifted verbatim into a standalone micro-lib the day
;; datahike needs to depend on it too (see relational-design-review-synthesis).
;;
;; The abstraction is Scallop's / Green et al.'s provenance semiring
;; (T, 0, 1, ⊕, ⊗) with the practical extensions Scallop adds:
;;   - `from-prob`  : a probability mass → a tag (input weights / proposal priors)
;;   - `weight`     : a tag → a real used to ORDER search (top-k / best-first)
;;   - `recover`    : a tag → the reported measure (double for discrete; a
;;                    sampler / Measure for a future continuous instance — kept
;;                    abstract so a quasi-Borel/sampling instance slots in beside
;;                    these without changing the interface)
;;   - `absorptive?`: is `t ⊕ (t ⊗ t') = t` (POPS)? Recursive datalog predicates
;;                    are only sound over an absorptive provenance (Scallop's
;;                    recursion constraint); an exact-WMC provenance is NOT
;;                    absorptive and must stay at the finite proof-tree level.
(ns ansatz.provenance)

(defprotocol IProvenance
  "A commutative semiring on a tag type T, with ordering/reporting extensions.
   Laws (documented; wandler CERTIFIES specific instances via WSemiring):
     ⊕,⊗ commutative+associative; ⊗ distributes over ⊕;
     zero = ⊕-identity + ⊗-annihilator; one = ⊗-identity."
  (prov-zero [P] "⊥ — the impossible/no-derivation tag (⊕ identity, ⊗ annihilator).")
  (prov-one [P] "⊤ — the trivial/certain tag (⊗ identity).")
  (prov-plus [P a b] "⊕ — combine ALTERNATIVE derivations (disjunction).")
  (prov-times [P a b] "⊗ — combine CONJOINED derivations (conjunction).")
  (prov-from-prob [P p] "A probability mass p∈(0,1] → a tag (input weight / proposal prior).")
  (prov-fact [P id p] "A LABELED uncertain fact `id` with credence p → a tag. Scalar
    semirings fold p like `from-prob` (ignoring the label); an exact-WMC
    provenance tracks `id` SYMBOLICALLY so the same fact used by alternative
    proofs is counted ONCE (correlation-aware). Default = from-prob.")
  (prov-weight [P a] "Tag → double: search-ordering key (HIGHER is explored first).")
  (prov-recover [P a] "Tag → the reported measure (double for discrete instances).")
  (prov-absorptive? [P] "True iff `a ⊕ (a ⊗ b) = a` — recursion-safe (POPS)."))

;; ---- Boolean: provability, no weighting ----
(defrecord BooleanProv []
  IProvenance
  (prov-zero [_] false)
  (prov-one [_] true)
  (prov-plus [_ a b] (or a b))
  (prov-times [_ a b] (and a b))
  (prov-from-prob [_ p] (pos? (double p)))
  (prov-fact [_ _ p] (pos? (double p)))
  (prov-weight [_ a] (if a 1.0 0.0))
  (prov-recover [_ a] a)
  (prov-absorptive? [_] true))

;; ---- MaxMinProb / Viterbi: tags are LOG-probabilities (≤ 0). ⊗ = ×, ⊕ = max.
;;      In log space ⊗ = +, ⊕ = max. This is the DEFAULT and is exactly the
;;      search measure ansatz.rel used before the refactor (best-proof score). ----
(defrecord MaxMinProbProv []
  IProvenance
  (prov-zero [_] Double/NEGATIVE_INFINITY)
  (prov-one [_] 0.0)
  (prov-plus [_ a b] (max (double a) (double b)))
  (prov-times [_ a b] (+ (double a) (double b)))
  (prov-from-prob [_ p] (Math/log (double p)))
  (prov-fact [_ _ p] (Math/log (double p)))  ; scalar fold, label ignored
  (prov-weight [_ a] (double a))            ; higher log-prob explored first
  (prov-recover [_ a] (Math/exp (double a))) ; back to a probability
  (prov-absorptive? [_] true))

;; ---- Tropical: tags are COSTS (≥ 0). ⊗ = +, ⊕ = min (shortest derivation). ----
(defrecord TropicalProv []
  IProvenance
  (prov-zero [_] Double/POSITIVE_INFINITY)
  (prov-one [_] 0.0)
  (prov-plus [_ a b] (min (double a) (double b)))
  (prov-times [_ a b] (+ (double a) (double b)))
  (prov-from-prob [_ p] (- (Math/log (double p)))) ; prob → cost
  (prov-fact [_ _ p] (- (Math/log (double p))))
  (prov-weight [_ a] (- (double a)))               ; lower cost explored first
  (prov-recover [_ a] a)
  (prov-absorptive? [_] true))

;; ---- ProofsProb: EXACT probability-of-provability by weighted model counting.
;;      A tag is a Boolean formula over LABELED fact-atoms, carried as a DNF —
;;      a set of CLAUSES, each clause a map {atom-id → credence} (a conjunction
;;      of facts). ⊗ = ∧ (cross-product+merge), ⊕ = ∨ (union of clauses). So the
;;      tag records EXACTLY which uncertain facts each alternative proof uses;
;;      `recover` is the WMC = P(formula true), which counts a fact SHARED by two
;;      proofs once (correlation-aware — unlike a naive independent-OR of proof
;;      probabilities). NOT absorptive: must stay at the finite proof-tree /
;;      certify level, never a recursive datalog fixpoint. ----
(defn- dnf-wmc
  "Weighted model count of a DNF (set of clause-maps {id→p}): the probability
   that some clause is fully satisfied, atoms independent with P(id)=p. Exact via
   enumeration over the atom set (fine for proof-sized formulas; a BDD/LogicNG
   backend slots in behind this for scale)."
  [dnf]
  (let [atoms (into {} (mapcat seq dnf))       ; id → p (consistent across clauses)
        ids (vec (keys atoms))
        n (count ids)]
    (cond
      (empty? dnf) 0.0                          ; ⊥  (no clause)
      (zero? n) 1.0                             ; ⊤  (contains the empty clause)
      :else
      (loop [i 0, acc 0.0]
        (if (= i (bit-shift-left 1 n))
          acc
          (let [true? (fn [id] (bit-test i (.indexOf ids id)))
                sat? (some (fn [clause] (every? (fn [[id _]] (true? id)) clause)) dnf)
                mass (reduce (fn [m id] (* m (let [p (atoms id)] (if (true? id) p (- 1.0 p)))))
                             1.0 ids)]
            (recur (inc i) (if sat? (+ acc mass) acc))))))))

(defrecord ProofsProb []
  IProvenance
  (prov-zero [_] #{})
  (prov-one [_] #{{}})
  (prov-plus [_ a b] (into a b))                         ; ∨ : union of clauses
  (prov-times [_ a b] (set (for [c1 a, c2 b] (merge c1 c2)))) ; ∧ : cross-product+merge
  (prov-from-prob [_ _] #{{}})                           ; proposal priors are NOT facts
  (prov-fact [_ id p] #{{id (double p)}})                ; a symbolic labeled atom
  (prov-weight [_ a] (dnf-wmc a))
  (prov-recover [_ a] (dnf-wmc a))                       ; P(provable)
  (prov-absorptive? [_] false))

(def boolean-prov (->BooleanProv))
(def maxminprob-prov (->MaxMinProbProv))
(def tropical-prov (->TropicalProv))
(def proofs-prov (->ProofsProb))

(def default-provenance
  "MaxMinProb (log). The behavior-preserving default for ansatz.rel: `condw`
   priors fold in via ⊗ (= +), disjunction via ⊕ (= max), best-first orders by
   `weight` (= the log-prob)."
  maxminprob-prov)
