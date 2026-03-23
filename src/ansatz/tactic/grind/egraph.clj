;; Persistent E-graph with congruence closure and propositional propagators.
;; Following Lean 4's grind tactic: Types.lean, Core.lean, Propagate.lean.
;;
;; Key advantage over Lean 4: Clojure's persistent data structures give
;; free backtracking — forking the E-graph for case splits is just keeping
;; a reference to the old map. No need for SavedState.restore.

(ns ansatz.tactic.grind.egraph
  "Persistent E-graph with congruence closure for the grind tactic.
   Pure Clojure — no external dependencies."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.tc :as tc]
            [ansatz.kernel.reduce :as red]))

;; ============================================================
;; Names (cached for performance)
;; ============================================================

(def ^:private true-name (name/from-string "True"))
(def ^:private false-name (name/from-string "False"))
(def ^:private eq-name (name/from-string "Eq"))
(def ^:private and-name (name/from-string "And"))
(def ^:private or-name (name/from-string "Or"))
(def ^:private not-name (name/from-string "Not"))
(def ^:private iff-name (name/from-string "Iff"))
(def ^:private ite-name (name/from-string "ite"))
(def ^:private bool-true-name (name/from-string "Bool.true"))
(def ^:private bool-false-name (name/from-string "Bool.false"))

;; ============================================================
;; ENode — one per internalized expression
;; Following Lean 4 Types.lean:447
;; ============================================================

(defn mk-enode
  "Create a fresh ENode for an expression."
  [expr idx gen]
  {:self    expr
   :next    expr      ;; circular linked list (initially points to self)
   :root    expr      ;; canonical representative (initially self)
   :congr   expr      ;; congruence class rep (initially self)
   :target  nil       ;; transitivity chain target (nil = is root)
   :proof   nil       ;; proof of self = target
   :flipped false     ;; whether proof is symmetric
   :size    1         ;; eqc size (only meaningful at root)
   :interp  false     ;; interpreted value (True, False, literals)
   :ctor    false     ;; constructor application
   :heq     false     ;; contains HEq proofs
   :gen     gen       ;; generation when created
   :mt      0         ;; modification time
   :idx     idx})     ;; unique index for debugging

;; ============================================================
;; GrindState — the E-graph + metadata
;; Following Lean 4 Types.lean:913
;; ============================================================

(declare internalize set-interpreted get-enode set-enode get-root get-root-node
         is-eqv is-eq-true is-eq-false get-parents add-congr-table
         propagate-up propagate-down)

(defn mk-grind-state
  "Create a fresh grind state. Internalizes True and False."
  [env]
  (let [true-expr  (e/const' true-name [])
        false-expr (e/const' false-name [])
        gs {:enodes      {}     ;; Expr -> ENode
            :parents     {}     ;; Expr -> #{parent-exprs}
            :congr-table {}     ;; congr-key -> Expr
            :app-map     {}     ;; head-name -> [Expr]
            :new-facts   []     ;; pending [{:lhs :rhs :proof :heq}]
            :inconsistent false
            :next-idx    0
            :gmt         0      ;; global modification time
            :true-expr   true-expr
            :false-expr  false-expr
            :env         env}]
    (-> gs
        (internalize true-expr 0)
        (set-interpreted true-expr)
        (internalize false-expr 0)
        (set-interpreted false-expr))))

;; ============================================================
;; ENode accessors
;; ============================================================

(defn get-enode
  "Look up the ENode for an expression. Returns nil if not internalized."
  [gs expr]
  (get (:enodes gs) expr))

(defn set-enode
  "Update the ENode for an expression."
  [gs expr node]
  (assoc-in gs [:enodes expr] node))

(defn get-root
  "Get the canonical representative of an expression's equivalence class."
  [gs expr]
  (if-let [node (get-enode gs expr)]
    (:root node)
    expr))

(defn get-root-node
  "Get the ENode of the canonical representative."
  [gs expr]
  (get-enode gs (get-root gs expr)))

(defn is-eqv
  "Check if two expressions are in the same equivalence class."
  [gs a b]
  (let [ra (get-root gs a)
        rb (get-root gs b)]
    (and ra rb (identical? ra rb))))

(defn is-eq-true
  "Check if an expression is equivalent to True."
  [gs expr]
  (is-eqv gs expr (:true-expr gs)))

(defn is-eq-false
  "Check if an expression is equivalent to False."
  [gs expr]
  (is-eqv gs expr (:false-expr gs)))

(defn- set-interpreted
  "Mark an expression's ENode as an interpreted value."
  [gs expr]
  (if-let [node (get-enode gs expr)]
    (set-enode gs expr (assoc node :interp true))
    gs))

;; ============================================================
;; Equivalence class traversal (circular linked list)
;; Following Lean 4 Types.lean:1490
;; ============================================================

(defn traverse-eqc
  "Traverse all expressions in an equivalence class. Calls (f expr) for each.
   Returns a vector of results."
  [gs expr f]
  (when-let [start-node (get-enode gs expr)]
    (loop [curr expr results []]
      (let [node (get-enode gs curr)
            results (conj results (f curr))
            next (:next node)]
        (if (identical? next expr)
          results
          (recur next results))))))

(defn collect-eqc
  "Collect all expressions in an equivalence class.
   Safety: stops after 10000 elements to prevent infinite loops."
  [gs expr]
  (when-let [start-node (get-enode gs expr)]
    (loop [curr expr results [] fuel 10000]
      (if (<= fuel 0)
        results  ;; safety cutoff
        (let [node (get-enode gs curr)]
          (if (nil? node)
            results
            (let [results (conj results curr)
                  next (:next node)]
              (if (or (identical? next expr) (nil? next))
                results
                (recur next results (dec fuel))))))))))

;; ============================================================
;; Congruence hashing and checking
;; Following Lean 4 Types.lean:545
;; ============================================================

(defn- congr-key
  "Compute a congruence key for an expression. Two expressions that should
   be congruent (same function applied to equivalent args) get the same key.
   For Eq: symmetric (treats a=b same as b=a)."
  [gs expr]
  (cond
    ;; Application: hash roots of function and argument
    (e/app? expr)
    (let [[head args] (e/get-app-fn-args expr)]
      (if (and (e/const? head) (= (e/const-name head) eq-name) (= 3 (count args)))
        ;; Eq is symmetric: use sorted hash of args 1 and 2
        (let [r1 (System/identityHashCode (get-root gs (nth args 1)))
              r2 (System/identityHashCode (get-root gs (nth args 2)))
              type-hash (System/identityHashCode (get-root gs (nth args 0)))]
          [:eq type-hash (min r1 r2) (max r1 r2)])
        ;; Normal application: hash roots of all args
        (let [root-hashes (mapv #(System/identityHashCode (get-root gs %)) args)
              head-hash (System/identityHashCode (get-root gs head))]
          [:app head-hash root-hashes])))

    ;; Forall: hash roots of domain and body
    (e/forall? expr)
    [:forall (System/identityHashCode (get-root gs (e/forall-type expr)))
             (System/identityHashCode (get-root gs (e/forall-body expr)))]

    ;; Everything else: unique key (no congruence)
    :else [:other (System/identityHashCode expr)]))

(defn- congruent?
  "Check if two expressions are congruent (same structure with equivalent args)."
  [gs e1 e2]
  (cond
    ;; Both applications
    (and (e/app? e1) (e/app? e2))
    (let [[h1 a1] (e/get-app-fn-args e1)
          [h2 a2] (e/get-app-fn-args e2)]
      (if (and (e/const? h1) (= (e/const-name h1) eq-name)
               (e/const? h2) (= (e/const-name h2) eq-name)
               (= 3 (count a1)) (= 3 (count a2)))
        ;; Eq: symmetric congruence check
        (and (is-eqv gs (nth a1 0) (nth a2 0))  ;; same type
             (or (and (is-eqv gs (nth a1 1) (nth a2 1))
                      (is-eqv gs (nth a1 2) (nth a2 2)))
                 (and (is-eqv gs (nth a1 1) (nth a2 2))
                      (is-eqv gs (nth a1 2) (nth a2 1)))))
        ;; Normal app: check head and all args
        (and (= (count a1) (count a2))
             (is-eqv gs h1 h2)
             (every? true? (map #(is-eqv gs %1 %2) a1 a2)))))

    ;; Both foralls
    (and (e/forall? e1) (e/forall? e2))
    (and (is-eqv gs (e/forall-type e1) (e/forall-type e2))
         (is-eqv gs (e/forall-body e1) (e/forall-body e2)))

    :else false))

;; ============================================================
;; Congruence table operations
;; ============================================================

(defn- add-congr-table
  "Add an expression to the congruence table. If a congruent expression already
   exists, push a new equality fact. Returns updated gs."
  [gs expr]
  (if (or (e/app? expr) (e/forall? expr))
    (let [key (congr-key gs expr)
          existing (get (:congr-table gs) key)]
      (if (and existing (not (identical? existing expr))
               (not (is-eqv gs existing expr)))
        ;; Found congruent partner — push new equality
        (-> gs
            (update :new-facts conj {:lhs existing :rhs expr
                                     :proof :congr-placeholder :heq false})
            (assoc-in [:congr-table key] expr))
        ;; No partner or already equivalent — just register
        (assoc-in gs [:congr-table key] expr)))
    gs))

(defn- remove-congr-table
  "Remove an expression from the congruence table."
  [gs expr]
  (if (or (e/app? expr) (e/forall? expr))
    (let [key (congr-key gs expr)]
      (if (identical? (get (:congr-table gs) key) expr)
        (update gs :congr-table dissoc key)
        gs))
    gs))

;; ============================================================
;; Parent tracking
;; ============================================================

(defn- register-parent
  "Register expr as a parent of child-expr."
  [gs child-expr parent-expr]
  (update-in gs [:parents (get-root gs child-expr)]
             (fnil conj #{}) parent-expr))

(defn- get-parents
  "Get the parent set for a root expression."
  [gs root-expr]
  (get-in gs [:parents root-expr] #{}))

;; ============================================================
;; Internalize — add a term to the E-graph
;; Following Lean 4 Internalize.lean
;; ============================================================

(defn internalize
  "Add an expression to the E-graph. Recursively internalizes children.
   Returns updated grind state."
  [gs expr gen]
  (if (get-enode gs expr)
    gs  ;; already internalized
    (let [idx (:next-idx gs)
          node (mk-enode expr idx gen)
          ;; Check if it's an interpreted value or constructor
          node (cond
                 (or (identical? expr (:true-expr gs))
                     (identical? expr (:false-expr gs))
                     (e/lit-nat? expr)
                     (e/lit-str? expr))
                 (assoc node :interp true)

                 (and (e/const? expr)
                      (when-let [ci (env/lookup (:env gs) (e/const-name expr))]
                        (.isCtor ^ansatz.kernel.ConstantInfo ci)))
                 (assoc node :ctor true)

                 (and (e/app? expr)
                      (let [[h _] (e/get-app-fn-args expr)]
                        (and (e/const? h)
                             (when-let [ci (env/lookup (:env gs) (e/const-name h))]
                               (.isCtor ^ansatz.kernel.ConstantInfo ci)))))
                 (assoc node :ctor true)

                 :else node)
          gs (-> gs
                 (assoc-in [:enodes expr] node)
                 (update :next-idx inc))]
      ;; Recursively internalize children and register parents
      (if (e/app? expr)
        (let [[head args] (e/get-app-fn-args expr)
              ;; Internalize head and all args
              gs (reduce (fn [gs child]
                           (-> (internalize gs child gen)
                               (register-parent child expr)))
                         gs (cons head args))
              ;; Add to app-map (indexed by head symbol)
              head-key (when (e/const? head) (e/const-name head))
              gs (if head-key
                   (update-in gs [:app-map head-key] (fnil conj []) expr)
                   gs)
              ;; Add to congruence table
              gs (add-congr-table gs expr)]
          gs)
        ;; Non-application: just return
        gs))))

;; ============================================================
;; Invert transitivity chain
;; Following Lean 4 Core.lean:26
;; ============================================================

(defn- invert-trans
  "Reverse the transitivity proof chain from expr toward the old root.
   After this, the chain goes from the old root toward expr."
  [gs expr]
  (loop [gs gs
         e expr
         flipped-new false
         target-new nil
         proof-new nil]
    (let [node (get-enode gs e)]
      (if-let [target (:target node)]
        ;; Continue walking the chain
        (recur (set-enode gs e (assoc node
                                      :target target-new
                                      :proof proof-new
                                      :flipped flipped-new))
               target
               (not (:flipped node))
               e
               (:proof node))
        ;; End of chain (was the root) — set final node
        (set-enode gs e (assoc node
                                :target target-new
                                :proof proof-new
                                :flipped flipped-new))))))

;; ============================================================
;; Update roots — set all nodes in a class to point to new root
;; ============================================================

(defn- update-roots
  "Walk the equivalence class of expr and set all roots to new-root."
  [gs expr new-root]
  (loop [gs gs curr expr fuel 10000]
    (if (<= fuel 0) gs
      (let [node (get-enode gs curr)]
        (if (nil? node) gs
          (let [gs (set-enode gs curr (assoc node :root new-root))
                next (:next node)]
            (if (or (identical? next expr) (nil? next))
              gs
              (recur gs next (dec fuel)))))))))

;; ============================================================
;; Remove and reinsert parents for congruence closure
;; Following Lean 4 Core.lean:49-66
;; ============================================================

(defn- remove-parents
  "Remove root's parents from the congruence table. Returns [gs parents]."
  [gs root-expr]
  (let [parents (get-parents gs root-expr)]
    [(reduce (fn [gs parent]
               (if (or (e/app? parent) (e/forall? parent))
                 (remove-congr-table gs parent)
                 gs))
             gs parents)
     parents]))

(defn- reinsert-parents
  "Re-add parents to congruence table, detecting new congruences."
  [gs parents]
  (reduce (fn [gs parent]
            (if (or (e/app? parent) (e/forall? parent))
              (add-congr-table gs parent)
              gs))
          gs parents))

;; ============================================================
;; Merge circular linked lists
;; Following Lean 4 Core.lean:226-234
;; ============================================================

(defn- merge-lists
  "Merge two circular linked lists by swapping next pointers.
   lhs-root and rhs-root are the roots of the two lists."
  [gs lhs-root-expr rhs-root-expr]
  (let [lhs-root-node (get-enode gs lhs-root-expr)
        rhs-root-node (get-enode gs rhs-root-expr)
        lhs-next (:next lhs-root-node)
        rhs-next (:next rhs-root-node)]
    (-> gs
        ;; lhs-root.next = rhs-root's old next
        (set-enode lhs-root-expr (assoc lhs-root-node :next rhs-next))
        ;; rhs-root.next = lhs-root's old next
        (set-enode rhs-root-expr (assoc rhs-root-node :next lhs-next)))))

;; ============================================================
;; Constructor theory — injection and discrimination
;; Following Lean 4 Ctor.lean
;; ============================================================

(declare push-eq)

(defn get-ctor-name
  "Get the constructor name from a constructor application, or nil."
  [expr]
  (let [[h _] (e/get-app-fn-args expr)]
    (when (e/const? h) (e/const-name h))))

(defn get-ctor-fields
  "Get the field arguments of a constructor application (skip params)."
  [env expr]
  (let [[h args] (e/get-app-fn-args expr)]
    (when (e/const? h)
      (let [ci (env/lookup env (e/const-name h))]
        (when (and ci (.isCtor ^ansatz.kernel.ConstantInfo ci))
          (let [ind-name (.inductName ^ansatz.kernel.ConstantInfo ci)
                ind-ci (env/lookup env ind-name)
                num-params (when ind-ci (.numParams ^ansatz.kernel.ConstantInfo ind-ci))]
            (when (and num-params (> (count args) num-params))
              (subvec (vec args) num-params))))))))

(defn- propagate-ctor
  "Handle constructor equality. Following Lean 4 Ctor.lean:
   - Same constructor: inject field equalities (a₁=b₁, a₂=b₂, ...)
   - Different constructor: mark inconsistent (contradiction)"
  [gs ctor-a-expr ctor-b-expr]
  (let [name-a (get-ctor-name ctor-a-expr)
        name-b (get-ctor-name ctor-b-expr)]
    (if (and name-a name-b)
      (if (= name-a name-b)
        ;; SAME constructor: inject field equalities
        (let [fields-a (get-ctor-fields (:env gs) ctor-a-expr)
              fields-b (get-ctor-fields (:env gs) ctor-b-expr)]
          (if (and fields-a fields-b (= (count fields-a) (count fields-b)))
            (reduce (fn [gs [fa fb]]
                      (if (.equals fa fb)
                        gs
                        (push-eq gs fa fb :ctor-injection)))
                    gs (map vector fields-a fields-b))
            gs))
        ;; DIFFERENT constructors: contradiction!
        (assoc gs :inconsistent true
                  :ctor-conflict [ctor-a-expr ctor-b-expr]))
      gs)))

;; ============================================================
;; Propagation dispatch
;; ============================================================

(declare propagate-up propagate-down)

;; ============================================================
;; Core merge algorithm — addEqStep
;; Following Lean 4 Core.lean:157-250
;; ============================================================

(defn add-eq
  "Merge two equivalence classes with a proof that lhs = rhs.
   This is the core of congruence closure.
   Returns updated grind state."
  [gs lhs rhs proof & {:keys [heq] :or {heq false}}]
  (let [lhs-root (get-root gs lhs)
        rhs-root (get-root gs rhs)]
    ;; Step 1: Already in same class?
    (if (identical? lhs-root rhs-root)
      gs
      (let [lhs-root-node (get-enode gs lhs-root)
            rhs-root-node (get-enode gs rhs-root)
            ;; Step 2: Check True=False inconsistency
            gs (if (and (:interp lhs-root-node) (:interp rhs-root-node)
                       (or (identical? lhs-root (:true-expr gs))
                           (identical? rhs-root (:true-expr gs)))
                       (or (identical? lhs-root (:false-expr gs))
                           (identical? rhs-root (:false-expr gs))))
                 (assoc gs :inconsistent true)
                 gs)]
        (if (:inconsistent gs)
          gs
          ;; Step 3: Choose merge direction
          ;; Keep interpreted/ctor/larger class as root
          (let [flip? (or (and (:interp lhs-root-node) (not (:interp rhs-root-node)))
                          (and (:ctor lhs-root-node) (not (:ctor rhs-root-node)))
                          (and (> (:size lhs-root-node) (:size rhs-root-node))
                               (not (:interp rhs-root-node))
                               (not (:ctor rhs-root-node))))
                [child parent child-node parent-node flipped?]
                (if flip?
                  [rhs lhs rhs-root-node lhs-root-node true]
                  [lhs rhs lhs-root-node rhs-root-node false])
                child-root (get-root gs child)
                parent-root (get-root gs parent)]

            ;; Step 4: Invert transitivity chain on child
            (let [gs (invert-trans gs child)
                  ;; Step 5: Set the new equality step
                  child-node-updated (get-enode gs child)
                  gs (set-enode gs child (assoc child-node-updated
                                                :target parent
                                                :proof proof
                                                :flipped flipped?))
                  ;; Step 6: Remove parents of old child-root from congr table
                  [gs parents] (remove-parents gs child-root)
                  ;; Step 7: Update all nodes in child's class to point to new root
                  gs (update-roots gs child parent-root)
                  ;; Step 8: Reinsert parents (detect new congruences)
                  gs (reinsert-parents gs parents)
                  ;; Step 9: Merge circular linked lists
                  gs (merge-lists gs child-root parent-root)
                  ;; Step 10: Update root metadata
                  parent-root-node (get-enode gs parent-root)
                  gs (set-enode gs parent-root
                               (assoc parent-root-node
                                      :size (+ (:size parent-root-node)
                                               (:size (get-enode gs child-root)))
                                      :heq (or heq (:heq parent-root-node)
                                               (:heq (get-enode gs child-root)))))
                  ;; Step 11: Copy parents from child-root to parent-root
                  child-parents (get-parents gs child-root)
                  gs (reduce (fn [gs p]
                               (update-in gs [:parents parent-root]
                                          (fnil conj #{}) p))
                             gs child-parents)
                  ;; Step 12: Update modification times
                  gs (update gs :gmt inc)
                  ;; Step 13: Propagate up on all parents
                  all-parents (into (get-parents gs parent-root) child-parents)
                  gs (reduce (fn [gs parent] (propagate-up gs parent))
                             gs all-parents)
                  ;; Step 14: Propagate down on merged class members
                  merged-members (collect-eqc gs child)
                  gs (reduce (fn [gs member] (propagate-down gs member))
                             gs (or merged-members []))
                  ;; Step 15: Constructor theory (Lean 4 Ctor.lean)
                  ;; If both roots were constructors, propagate injection or discrimination
                  gs (if (and (not (:inconsistent gs))
                              (:ctor (get-enode gs child-root))
                              (:ctor (get-enode gs parent-root)))
                       (propagate-ctor gs child-root parent-root)
                       gs)]
              gs)))))))

;; ============================================================
;; Process pending facts queue
;; ============================================================

(def ^:dynamic *max-facts-fuel*
  "Maximum number of facts to process before stopping.
   Lean 4 uses heartbeat checks; we use a simple counter."
  10000)

(defn process-new-facts
  "Drain the new-facts queue, merging each equality.
   Loops until queue is empty, inconsistent, or fuel exhausted."
  [gs]
  (loop [gs gs fuel *max-facts-fuel*]
    (if (or (:inconsistent gs) (empty? (:new-facts gs)) (<= fuel 0))
      gs
      (let [fact (first (:new-facts gs))
            gs (update gs :new-facts subvec 1)
            gs (add-eq gs (:lhs fact) (:rhs fact) (:proof fact)
                       :heq (or (:heq fact) false))]
        (recur gs (dec fuel))))))

;; ============================================================
;; Propositional propagators
;; Following Lean 4 Propagate.lean
;; ============================================================

(defn- get-app-head-name
  "Get the head constant name of an application, or nil."
  [expr]
  (let [[h _] (e/get-app-fn-args expr)]
    (when (e/const? h) (e/const-name h))))

(defn- get-app-args
  "Get the arguments of an application."
  [expr]
  (let [[_ args] (e/get-app-fn-args expr)]
    args))

(defn- push-eq
  "Push a new equality fact onto the queue."
  [gs lhs rhs proof]
  (update gs :new-facts conj {:lhs lhs :rhs rhs :proof proof :heq false}))

(defn- push-eq-true
  "Push fact: expr = True."
  [gs expr proof]
  (push-eq gs expr (:true-expr gs) proof))

(defn- push-eq-false
  "Push fact: expr = False."
  [gs expr proof]
  (push-eq gs expr (:false-expr gs) proof))

;; --- And propagators ---

(defn- propagate-and-up
  "Propagate truth values UP through And.
   a=T → (a∧b)=b | b=T → (a∧b)=a | a=F → (a∧b)=F | b=F → (a∧b)=F"
  [gs expr]
  (let [args (get-app-args expr)]
    (when (= 2 (count args))
      (let [a (nth args 0) b (nth args 1)]
        (cond
          (is-eq-true gs a)  (push-eq gs expr b {:tag :and-eq-true-left :a a :b b})
          (is-eq-true gs b)  (push-eq gs expr a {:tag :and-eq-true-right :a a :b b})
          (is-eq-false gs a) (push-eq-false gs expr {:tag :and-eq-false-left :a a :b b})
          (is-eq-false gs b) (push-eq-false gs expr {:tag :and-eq-false-right :a a :b b})
          :else nil)))))

(defn- propagate-and-down
  "Propagate truth values DOWN through And.
   (a∧b)=T → a=T, b=T"
  [gs expr]
  (when (is-eq-true gs expr)
    (let [args (get-app-args expr)]
      (when (= 2 (count args))
        (let [a (nth args 0) b (nth args 1)]
          (-> gs
              (push-eq-true a {:tag :and-true-left :ab expr})
              (push-eq-true b {:tag :and-true-right :ab expr})))))))

;; --- Or propagators ---

(defn- propagate-or-up
  "Propagate truth values UP through Or.
   a=F → (a∨b)=b | b=F → (a∨b)=a | a=T → (a∨b)=T | b=T → (a∨b)=T"
  [gs expr]
  (let [args (get-app-args expr)]
    (when (= 2 (count args))
      (let [a (nth args 0) b (nth args 1)]
        (cond
          (is-eq-false gs a) (push-eq gs expr b {:tag :or-eq-false-left :a a :b b})
          (is-eq-false gs b) (push-eq gs expr a {:tag :or-eq-false-right :a a :b b})
          (is-eq-true gs a)  (push-eq-true gs expr {:tag :or-eq-true-left :a a :b b})
          (is-eq-true gs b)  (push-eq-true gs expr {:tag :or-eq-true-right :a a :b b})
          :else nil)))))

(defn- propagate-or-down
  "Propagate truth values DOWN through Or.
   (a∨b)=F → a=F, b=F"
  [gs expr]
  (when (is-eq-false gs expr)
    (let [args (get-app-args expr)]
      (when (= 2 (count args))
        (let [a (nth args 0) b (nth args 1)]
          (-> gs
              (push-eq-false a {:tag :or-false-left :ab expr})
              (push-eq-false b {:tag :or-false-right :ab expr})))))))

;; --- Not propagators ---

(defn- propagate-not-up
  "Propagate truth values UP through Not.
   a=F → ¬a=T | a=T → ¬a=F"
  [gs expr]
  (let [args (get-app-args expr)]
    (when (= 1 (count args))
      (let [a (nth args 0)]
        (cond
          (is-eq-false gs a) (push-eq-true gs expr {:tag :not-eq-false :a a})
          (is-eq-true gs a)  (push-eq-false gs expr {:tag :not-eq-true :a a})
          :else nil)))))

(defn- propagate-not-down
  "Propagate truth values DOWN through Not.
   ¬a=T → a=F | ¬a=F → a=T"
  [gs expr]
  (let [args (get-app-args expr)]
    (when (= 1 (count args))
      (let [a (nth args 0)]
        (cond
          (is-eq-true gs expr)  (push-eq-false gs a {:tag :not-true-inner :not-a expr})
          (is-eq-false gs expr) (push-eq-true gs a {:tag :not-false-inner :not-a expr})
          :else nil)))))

;; --- Eq (Prop-valued) propagators ---

(defn- propagate-eq-up
  "Propagate truth values UP through Eq.
   a~b → (a=b)=T | a=T,b=T → (a=b)=T | a=F,b=F → (a=b)=T"
  [gs expr]
  (let [args (get-app-args expr)]
    (when (= 3 (count args))
      (let [_ty (nth args 0) a (nth args 1) b (nth args 2)]
        (cond
          ;; a and b are in same equivalence class
          (is-eqv gs a b)
          (push-eq-true gs expr {:tag :eq-refl :a a :b b})
          ;; Both true or both false
          (and (is-eq-true gs a) (is-eq-true gs b))
          (push-eq-true gs expr {:tag :eq-both-true :a a :b b})
          (and (is-eq-false gs a) (is-eq-false gs b))
          (push-eq-true gs expr {:tag :eq-both-false :a a :b b})
          ;; One true, one false
          (and (is-eq-true gs a) (is-eq-false gs b))
          (push-eq-false gs expr {:tag :eq-true-false :a a :b b})
          (and (is-eq-false gs a) (is-eq-true gs b))
          (push-eq-false gs expr {:tag :eq-false-true :a a :b b})
          :else nil)))))

(defn- propagate-eq-down
  "Propagate truth values DOWN through Eq.
   (a=b)=T → merge a and b"
  [gs expr]
  (when (is-eq-true gs expr)
    (let [args (get-app-args expr)]
      (when (= 3 (count args))
        (let [a (nth args 1) b (nth args 2)]
          (when-not (is-eqv gs a b)
            (push-eq gs a b {:tag :eq-true-merge :eq-expr expr})))))))

;; --- ite propagators ---

(defn- propagate-ite-up
  "Propagate truth values UP through ite.
   c=T → ite(c,t,e)=t | c=F → ite(c,t,e)=e"
  [gs expr]
  ;; ite : {α : Sort u} → (c : Prop) → [Decidable c] → α → α → α
  ;; args: [α, c, inst, t, e]
  (let [args (get-app-args expr)]
    (when (= 5 (count args))
      (let [c (nth args 1) t (nth args 3) e-branch (nth args 4)]
        (cond
          (is-eq-true gs c)  (push-eq gs expr t {:tag :ite-true :c c})
          (is-eq-false gs c) (push-eq gs expr e-branch {:tag :ite-false :c c})
          :else nil)))))

;; ============================================================
;; Propagation dispatch
;; ============================================================

(defn propagate-up
  "Dispatch UP propagators based on head symbol."
  [gs expr]
  (if (:inconsistent gs)
    gs
    (if-let [head-name (get-app-head-name expr)]
      (or (cond
            (= head-name and-name) (propagate-and-up gs expr)
            (= head-name or-name)  (propagate-or-up gs expr)
            (= head-name not-name) (propagate-not-up gs expr)
            (= head-name eq-name)  (propagate-eq-up gs expr)
            (= head-name ite-name) (propagate-ite-up gs expr)
            :else nil)
          gs)
      gs)))

(defn propagate-down
  "Dispatch DOWN propagators based on head symbol."
  [gs expr]
  (if (:inconsistent gs)
    gs
    (if-let [head-name (get-app-head-name expr)]
      (or (cond
            (= head-name and-name) (propagate-and-down gs expr)
            (= head-name or-name)  (propagate-or-down gs expr)
            (= head-name not-name) (propagate-not-down gs expr)
            (= head-name eq-name)  (propagate-eq-down gs expr)
            :else nil)
          gs)
      gs)))

;; ============================================================
;; High-level API
;; ============================================================

(defn assert-eq
  "Assert an equality lhs = rhs with proof, process all consequences.
   Returns updated grind state."
  [gs lhs rhs proof]
  (-> gs
      (add-eq lhs rhs proof)
      process-new-facts))

(defn assert-true
  "Assert that expr is True (with proof). Process consequences."
  [gs expr proof]
  (assert-eq gs expr (:true-expr gs) proof))

(defn assert-false
  "Assert that expr is False (with proof). Process consequences."
  [gs expr proof]
  (assert-eq gs expr (:false-expr gs) proof))
