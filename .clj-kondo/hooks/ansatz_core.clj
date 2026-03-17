(ns hooks.ansatz-core
  "clj-kondo hooks for ansatz.core macros: defn, theorem, inductive.

   These macros have custom syntax with type annotations that kondo
   doesn't understand. The hooks rewrite them to standard Clojure forms
   so kondo can analyze bindings and references properly."
  (:require [clj-kondo.hooks-api :as api]))

;; ================================================================
;; Helpers
;; ================================================================

(defn- strip-type-annotations
  "Remove :- Type pairs and bare type annotations from a parameter vector.
   Input:  [n :- Nat, x Real]  or  [n Nat]
   Output: [n x]  or  [n]

   ansatz params use two formats:
   - [name :- Type, ...] — annotated
   - [name Type, ...]    — positional (every other element is type)

   We strip ':- Type' pairs and also handle positional by taking every other."
  [param-nodes]
  (loop [nodes (seq param-nodes)
         acc []]
    (if-not nodes
      acc
      (let [node (first nodes)
            v (api/sexpr node)]
        (cond
          ;; Skip commas
          (and (api/token-node? node) (= ', v))
          (recur (next nodes) acc)

          ;; :- annotation: skip :- and the type that follows
          (and (api/keyword-node? node) (= :- v))
          (recur (nnext nodes) acc)

          ;; Check if NEXT is :- (annotated form)
          (and (next nodes)
               (let [nxt (second nodes)]
                 (and (api/keyword-node? nxt) (= :- (api/sexpr nxt)))))
          ;; Keep the name, skip :- and type
          (recur (nnnext nodes) (conj acc node))

          ;; Positional form: name Type name Type ...
          ;; Take every other (name, skip type)
          (and (next nodes)
               (api/token-node? node)
               (symbol? v)
               ;; Next should be a type (symbol or list)
               (let [nxt (second nodes)]
                 (or (api/token-node? nxt) (api/list-node? nxt))))
          (recur (nnext nodes) (conj acc node))

          ;; Default: keep
          :else
          (recur (next nodes) (conj acc node)))))))

(defn- nnnext [s]
  (-> s next next next))

;; ================================================================
;; (a/defn fn-name [params...] RetType body)
;; → (def fn-name (fn [stripped-params] body))
;; ================================================================

(defn ansatz-defn
  "Hook for (a/defn name [params] ret-type body).
   Rewrites to (def name (fn [params'] body)) stripping type annotations."
  [{:keys [node]}]
  (let [children (rest (:children node))  ;; skip 'defn
        fn-name (first children)
        params-node (second children)
        ;; ret-type is the 3rd, body is the 4th
        body (nth children 3 nil)
        ;; Strip type annotations from params
        param-children (when params-node (:children params-node))
        stripped (strip-type-annotations param-children)
        new-params (api/vector-node stripped)]
    {:node (api/list-node
            (list* (api/token-node 'def)
                   fn-name
                   (when body
                     [(api/list-node
                       (list (api/token-node 'fn)
                             new-params
                             body))])))}))

;; ================================================================
;; (a/theorem thm-name [params] prop tactic1 tactic2 ...)
;; → (do nil) — theorems have no runtime bindings to track
;; ================================================================

(defn ansatz-theorem
  "Hook for (a/theorem name [params] prop & tactics).
   Theorems don't produce runtime bindings, so we emit (do nil)."
  [{:keys [_node]}]
  {:node (api/list-node
          [(api/token-node 'do)
           (api/token-node 'nil)])})

;; ================================================================
;; (a/inductive TypeName [params] (ctor1 [fields]) (ctor2 [fields]))
;; → (do nil) — inductive types are kernel-level, no Clojure bindings
;; ================================================================

(defn ansatz-inductive
  "Hook for (a/inductive Name [params] & ctors).
   Inductive types don't produce Clojure bindings, so we emit (do nil)."
  [{:keys [_node]}]
  {:node (api/list-node
          [(api/token-node 'do)
           (api/token-node 'nil)])})
