(ns ansatz.wf-supplement
  "Strict schema-2 WF roles, separate from the shipped schema-1 legacy loader.
   Pure preparation returns an unactivated ProofContext; the explicit convenience
   entry conditionally installs it. Integrity/provenance records do not replace
   declaration compatibility."
  (:require [clojure.walk :as walk]
            [ansatz.artifact-profile :as profile]
            [ansatz.bundle :as bundle]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.companion-overlay :as overlay]
            [ansatz.export.evidence :as evidence]
            [ansatz.export.role-input :as input]
            [ansatz.export.replay :as replay]
            [ansatz.export.storage :as storage]
            [ansatz.kernel.constant-info :as ci]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.quotient :as quotient]
            [ansatz.session :as session])
  (:import [ansatz.kernel ConstantInfo ConstantInfo$RecursorRule Env Name Expr]
           [java.util ArrayDeque IdentityHashMap]))

(def ^:private option-keys
  #{:bundle-options :input-limits :candidate-limits :store-evidence-limits :comparison-limits :overlay-limits})
(def ^:private sentinels {:lex "Prod.Lex.right'" :sizeof "List._sizeOf_inst"})
(defn- fail [message data] (throw (ex-info message (assoc data :type ::refused))))

(defn- packages!
  "Validate actual raw-record membership after bounded CI assembly. Ordinary
   recursor names are semantic: Lean v4.33.1 (819816b2),
   src/kernel/inductive.cpp:mk_rec_name is
   I + `rec`, and declare_recursors emits one primary recursor per ordinary head.
   Nested auxiliary closure is deliberately unsupported here, never guessed."
  [{:keys [decls inductive-groups]}]
  (let [covered (volatile! #{})
        packages
        (mapv
         (fn [{:keys [start end head-count ctor-count recursor-count]}]
           (when-not (and (every? #(and (integer? %) (<= 0 % (count decls)))
                                  [start end head-count ctor-count recursor-count])
                          (pos? head-count) (<= start end)
                          (= (- end start) (+ head-count ctor-count recursor-count)))
             (fail "Incomplete ordinary inductive record" {:stage :package-closure}))
           (let [members (subvec decls start end)
                 heads (subvec members 0 head-count)
                 ctors (subvec members head-count (+ head-count ctor-count))
                 recursors (subvec members (+ head-count ctor-count))
                 head-names (mapv #(.name ^ConstantInfo %) heads)
                 head-set (set head-names)
                 ctor-set (set (map #(.name ^ConstantInfo %) ctors))]
             (when-not (and (every? #(.isInduct ^ConstantInfo %) heads)
                            (every? #(.isCtor ^ConstantInfo %) ctors)
                            (every? #(.isRecursor ^ConstantInfo %) recursors))
               (fail "Inductive record has inconsistent variant sections" {:stage :package-closure}))
             (when (some #(pos? (.numNested ^ConstantInfo %)) heads)
               (fail "Strict WF v1 does not support nested inductive packages"
                     {:stage :package-closure :reason :unsupported-nested-package}))
             (when-not (= head-count recursor-count)
               (fail "Ordinary inductive record omits primary recursors" {:stage :package-closure}))
             (doseq [^ConstantInfo head heads]
               (when-not (= head-names (vec (.all head)))
                 (fail "Inductive record omits or reorders mutual heads" {:stage :package-closure}))
               (let [supplied (filterv #(= (.name head) (.inductName ^ConstantInfo %)) ctors)]
                 (when-not (and (= (vec (.ctors head)) (mapv #(.name ^ConstantInfo %) supplied))
                                (= (vec (range (count supplied))) (mapv #(.cidx ^ConstantInfo %) supplied)))
                   (fail "Inductive record does not contain its exact constructor table" {:stage :package-closure}))))
             (when-not (every? #(contains? head-set (.inductName ^ConstantInfo %)) ctors)
               (fail "Constructor belongs to another inductive record" {:stage :package-closure}))
             (when-not (= (mapv #(Name/mkStr % "rec") head-names)
                          (mapv #(.name ^ConstantInfo %) recursors))
               (fail "Ordinary inductive record lacks exact primary recursors" {:stage :package-closure}))
             (doseq [^ConstantInfo recursor recursors]
               (when-not (= head-names (vec (.all recursor)))
                 (fail "Recursor describes another mutual package" {:stage :package-closure}))
               (doseq [^ConstantInfo$RecursorRule rule (.rules recursor)]
                 (when-not (contains? ctor-set (.ctor rule))
                   (fail "Recursor rule references a constructor outside its record" {:stage :package-closure}))))
             (doseq [i (range start end)]
               (when (contains? @covered i) (fail "Overlapping raw inductive records" {:stage :package-closure}))
               (vswap! covered conj i))
             {:kind :inductive :names (mapv #(.name ^ConstantInfo %) members)}))
         inductive-groups)
        quots (filterv #(.isQuot ^ConstantInfo %) decls)]
    (doseq [[index ^ConstantInfo declaration] (map-indexed vector decls)]
      (when (and (contains? #{5 6 7} (int (.tag declaration))) (not (contains? @covered index)))
        (fail "Inductive declaration has no original raw record" {:stage :package-closure})))
    (when (seq quots) (quotient/validate-package! quots))
    (cond-> packages (seq quots) (conj {:kind :quotient :names (mapv #(.name ^ConstantInfo %) quots)}))))

(defn- letter-like? [c]
  ;; Lean v4.33.1 Init/Meta/Defs.lean:isLetterLike, used by Name.toString.
  (or (and (<= 0x3b1 c 0x3c9) (not= c 0x3bb))
      (and (<= 0x391 c 0x3a9) (not (contains? #{0x3a0 0x3a3} c)))
      (<= 0x3ca c 0x3fb) (<= 0x1f00 c 0x1ffe) (<= 0x2100 c 0x214f)
      (<= 0x1d49c c 0x1d59f)
      (and (<= 0x00c0 c 0x00ff) (not (contains? #{0x00d7 0x00f7} c)))
      (<= 0x0100 c 0x017f)))

(defn- bare-component? [^String text]
  (and (pos? (.length text))
       (loop [i 0]
         (if (= i (.length text)) true
             (let [c (.codePointAt text i)
                   first? (zero? i)
                   initial? (or (<= 65 c 90) (<= 97 c 122) (= c 95) (letter-like? c))
                   rest? (or initial? (<= 48 c 57) (contains? #{39 33 63} c)
                             (<= 0x2080 c 0x2089) (<= 0x2090 c 0x209c)
                             (<= 0x1d62 c 0x1d6a) (= c 0x2c7c))]
               (and (if first? initial? rest?) (recur (+ i (Character/charCount c)))))))))

(defn- check-name-text! [declarations]
  ;; Companion profile 1 and existing consumers use dotted text names. Refuse
  ;; global components that Lean would escape but Java Name.toString/fromString
  ;; cannot faithfully join. This is a strict-v1 refusal, not a legacy parser change.
  (let [seen (IdentityHashMap.)]
    (doseq [^ConstantInfo declaration declarations]
      (when (= 0 (int (.tag (.name declaration))))
        (fail "Strict role declaration cannot be anonymous" {:stage :name-encoding}))
      (loop [^Name n (.name declaration)]
        (when-not (.containsKey seen n)
          (.put seen n true)
          (when (and (= 1 (int (.tag n))) (not (bare-component? (.str n))))
            (fail "Strict WF v1 cannot join an escaped declaration name to companion text"
                  {:stage :name-encoding :reason :unsupported-name-encoding}))
          (when (pos? (int (.tag n))) (recur (.prefix n))))))))

(defn- check-kernel-closure! [declarations names]
  ;; One extra iterative pass over already bounded candidate DAGs, not another
  ;; decoder or unbounded equality walk. Materialization already bounded every
  ;; root array, unique Expr node, edge and reachable Name prefix/string.
  (let [stack (ArrayDeque.) seen (IdentityHashMap.)]
    (doseq [^ConstantInfo declaration declarations]
      (.push stack (.type declaration))
      (when-let [body (.value declaration)] (.push stack body))
      (doseq [^ConstantInfo$RecursorRule rule (.rules declaration)] (.push stack (.rhs rule))))
    (while (not (.isEmpty stack))
      (let [^Expr expression (.pop stack)]
        (when-not (.containsKey seen expression)
          (.put seen expression true)
          (case (int (.tag expression))
            2 (when-not (contains? names (.o0 expression))
                (fail "Kernel dependency is outside the actual standalone role export" {:stage :kernel-closure}))
            3 (do (.push stack (.o0 expression)) (.push stack (.o1 expression)))
            (4 5) (do (.push stack (.o1 expression)) (.push stack (.o2 expression)))
            6 (do (.push stack (.o1 expression)) (.push stack (.o2 expression)) (.push stack (.o3 expression)))
            (9 10) (.push stack (.o1 expression))
            (0 1 7 8 11) nil
            (fail "Unsupported candidate expression in kernel closure" {:stage :kernel-closure})))))))

(defn- overlap-and-missing [^Env base declarations packages evidence-limits comparison-limits]
  (let [local (into {} (keep (fn [^ConstantInfo candidate]
                               (when-let [existing (.lookupLocal base (.name candidate))]
                                 [(.name candidate) existing]))) declarations)
        external-names (into [] (comp (map #(.name ^ConstantInfo %)) (remove #(contains? local %))) declarations)
        ;; No ordinary Env.lookup partitions the PSS view. This one scoped
        ;; invocation validates Names, proves absence and builds only full CIs.
        stored (if (seq external-names)
                 (storage/full-ci-evidence-partition base external-names evidence-limits)
                 {:constants {} :absent []})
        absent (set (:absent stored))]
    (doseq [{:keys [kind names]} packages]
      (let [missing (filterv absent names)]
        (when (and (seq missing) (not= (count missing) (count names)))
          (fail "Strict WF v1 refuses a partially present package"
                {:stage :base-partition :reason :unsupported-partial-package :kind kind
                 :package-names (mapv str names) :missing-names (mapv str missing)}))))
    (let [pairs (into [] (keep (fn [^ConstantInfo candidate]
                                 (when-not (contains? absent (.name candidate))
                                   [(or (get local (.name candidate))
                                        (get (:constants stored) (.name candidate))) candidate]))) declarations)]
      (when-not (ci/full-equal-batch-bounded? pairs comparison-limits)
        (fail "WF supplement differs from complete base declaration evidence" {:stage :overlap})))
    ;; Full stored proof bodies do not escape this check into normal Env caches.
    {:missing (filterv #(contains? absent (.name ^ConstantInfo %)) declarations)
     :present (into {} (keep (fn [^ConstantInfo declaration]
                               (when-not (contains? absent (.name declaration))
                                 [(.name declaration) declaration]))) declarations)}))

(defn- replay-isolated [^Env original {:keys [missing present]} packages]
  ;; A closed projection of an already trusted Env may be used by the checker
  ;; after every retained CI matched exactly. No store resolver or shared cache
  ;; participates in this temporary view, and missing headers stay absent until
  ;; the existing strict replay protocol admits them.
  (check-kernel-closure! (vec (vals present)) (set (keys present)))
  (let [quot-package (first (filter #(= :quotient (:kind %)) packages))
        matched-quot? (and quot-package (every? #(contains? present %) (:names quot-package)))
        missing-quot? (and quot-package (not matched-quot?))]
    (when (and quot-package (not= (boolean matched-quot?) (.isQuotEnabled original)))
      (fail "Captured quotient state does not match the complete role package" {:stage :builtin-state}))
    (let [initial (.withExternalLookupUncached (Env.) present (count present))
          initial (if matched-quot? (.enableQuot initial) initial)
          result (replay/replay-from-env initial missing :verify? true :stop-on-error? true)
          ^Env checked (:env result)
          expected (set (map #(.name ^ConstantInfo %) missing))
          _ (when (> (.size checked) (+ (count present) (count missing)))
              (fail "Isolated replay produced excess declarations" {:stage :replay-closure}))
          admitted (vec (.allConstants checked))]
      (when-not (and (zero? (get-in result [:stats :errors]))
                     (= (count missing) (get-in result [:stats :total]))
                     (= expected (set (map #(.name ^ConstantInfo %) admitted))))
        (fail "Isolated replay did not admit exactly the missing role declarations" {:stage :replay-closure}))
      (when (not= (boolean (or matched-quot? missing-quot?)) (.isQuotEnabled checked))
        (fail "Isolated replay changed unsupported special builtin state" {:stage :builtin-state}))
      (let [restored
            (reduce (fn [^Env current ^ConstantInfo candidate]
                      (let [actual (.lookupLocal checked (.name candidate))]
                        (when-not actual (fail "Checked missing declaration was not local" {:stage :transplant}))
                        ;; Keep the kernel duplicate guard. This is exactly one
                        ;; further ordinary name-tree point lookup per missing
                        ;; CI (bounded by candidate :declarations). The captured
                        ;; stable handler sees the same absent raw shell, so it
                        ;; cannot enter Expr/name/level hydration on this miss.
                        ;; No existing CI is replaced or proof body cached.
                        (.addConstant current actual))) original missing)]
        (if missing-quot? (.enableQuot restored) restored)))))

(defn- selected-companions [names input-limits]
  (let [all (into {} (map (fn [role] [role (bundle/verified-companion-rows role)])) [:attrs :matchers :instances])]
    (when (> (reduce +' 0 (map count (vals all))) (:companion-rows input-limits))
      (fail "Captured companion row volume exceeded" {:stage :metadata :limit :companion-rows}))
    (let [selected (into {} (map (fn [[role rows]] [role (filterv #(contains? names (:name %)) rows)])) all)
          ;; Verified matcher discriminants are local annotations, not global
          ;; dependency edges (bundle-metadata/references contract). Avoid walking
          ;; their nested local tables until overlay's bounded metadata preflight.
          edges (concat (metadata/references :attrs (:attrs selected))
                        (metadata/references :instances (:instances selected)))]
      (doseq [{:keys [source target]} edges]
        (when-not (contains? names target)
          (fail "Selected companion reference is outside the actual role export"
                {:stage :metadata-closure :source source :target target})))
      selected)))

(defn prepare-strict-role
  "Prepare an unactivated complete ProofContext for :lex or :sizeof using one
   verified schema-2 snapshot. captured must come from session/capture. Options
   explicitly supply :bundle-options, :input-limits, :candidate-limits,
   :store-evidence-limits, :comparison-limits and :overlay-limits.
   All overlap uses complete bounded CI evidence; only whole absent packages are
   strictly replayed in an isolated Env. Parser resources close before return.
   Neither a sentinel nor an artifact profile skips proof/closure checks. Existing
   base TRUST provenance is retained; exact overlap does not kernel-check the base.
   Strict v1 refuses nested/partial packages and declaration components requiring
   Lean text escapes unsupported by existing companion-name consumers.
   Does not activate or mutate global session slots. Shipped legacy WF entry
   points are unchanged. Candidate decoding remains trusted export infrastructure."
  [captured role options]
  (when-not (and (contains? sentinels role) (instance? Env (:env captured))
                 (map? options) (= option-keys (set (keys options))) (every? map? (vals options)))
    (fail "Invalid strict WF preparation request" {:stage :request}))
  (let [base (:env captured)
        prior-profile (env/get-extension base profile/extension-key nil)
        requirements (profile/supplemental-requirements prior-profile)
        bundle-options (update (:bundle-options options) :requirements
                               (fn [caller]
                                 (doseq [[key value] requirements]
                                   (when (and (contains? caller key) (not= value (get caller key)))
                                     (fail "Explicit bundle requirements contradict captured base" {:stage :cohort})))
                                 (merge caller requirements)))]
    (bundle/with-verified
      bundle-options
      (fn [manifest]
        (when-not (= "ansatz-bundle/2" (:bundle/schema manifest))
          (fail "Strict WF preparation requires schema-2 companion provenance; use the explicit legacy path otherwise"
                {:stage :provenance :reason :unsupported-legacy-evidence}))
        (bundle/assert-consumable!)
        (input/with-candidate
          (bundle/verified-bytes (get bundle/role-resources role))
          (:input-limits options) (:candidate-limits options)
          (fn [{:keys [decls meta] :as candidate}]
            ;; Parser metadata keeps JSON string keys; the verified manifest
            ;; uses keyword keys. Normalize the bounded producer schema only.
            (when-not (= meta (walk/stringify-keys (:producer manifest)))
              (fail "Raw candidate producer differs from the captured snapshot" {:stage :provenance}))
            (check-name-text! decls)
            (let [packages (packages! candidate)
                  name-objects (set (map #(.name ^ConstantInfo %) decls))
                  names (into #{} (map str) name-objects)]
              (let [roots (get-in manifest [:generation :roots role])]
                (when-not (and (<= (count roots) (count names))
                               (every? names roots) (contains? names (get sentinels role)))
                  (fail "Selected role does not export its actual recipe roots" {:stage :role-closure})))
              (check-kernel-closure! decls name-objects)
              (let [rows (selected-companions names (:input-limits options))
                    partition (overlap-and-missing base decls packages (:store-evidence-limits options)
                                                   (:comparison-limits options))
                    checked (replay-isolated base partition packages)
                    prepared (overlay/prepare-session captured checked rows names (:overlay-limits options))
                    ;; Descriptive history only, written after actual checks.
                    description {:kernel-role role :cohort (:artifact/cohort manifest)
                                 :overlap :full-exact :missing-admission :checked
                                 :companions :strict-selected-role}
                    history (or (:supplements prior-profile) [])
                    _ (when-not (and (vector? history) (<= (count history) 2)
                                     (every? #(contains? sentinels (:kernel-role %)) history)
                                     (= (count history) (count (set (map :kernel-role history)))))
                        (fail "Strict WF v1 requires a bounded two-role supplement history" {:stage :profile}))
                    ;; Keep one description per role. This presentation update
                    ;; never skips any checks and cannot grow under alternation.
                    history (conj (filterv #(not= role (:kernel-role %)) history) description)
                    next-profile (assoc (or prior-profile {:schema profile/schema :base {:kind :unknown} :roles {}})
                                        :supplements history)]
                (assoc prepared :env (env/with-extension (:env prepared) profile/extension-key next-profile))))))))))


(defn activate-strict-role!
  "Capture the live session, prepare a strict schema-2 role outside the long
   session lock, then conditionally install it once. Requires the same explicit
   finite options as prepare-strict-role. Returns the activated ProofContext.
   A stale/rejected/failed installation throws ExceptionInfo with :outcome and
   the original installation :cause; no retry or legacy fallback occurs.
   Preparation errors propagate before any owned installation. Captured store
   resources remain borrowed and their owner must keep them alive throughout
   preparation. Unlocked global mutations remain outside cooperative isolation."
  [role options]
  (let [captured (session/capture)
        prepared (prepare-strict-role captured role options)
        outcome (session/activate-if-unchanged! captured prepared)]
    (if (= :activated (:status outcome))
      (:session outcome)
      (throw (ex-info "Strict WF role activation did not complete"
                      {:type ::activation-refused :role role :outcome outcome}
                      (:cause outcome))))))
