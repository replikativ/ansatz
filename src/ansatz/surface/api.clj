(ns ansatz.surface.api
  "The STABLE extension-author API for surface elaborators (what a runtime like wandler
   builds against — depend on this, never on elaborator internals).

   Two registries, mirroring lean4's two extension points:
     macro_rules  — (a/register-elaborator! 'sym (fn [args] surface-form))
                    syntax → syntax; the result re-elaborates.
     elab_rules   — (a/register-term-elaborator! 'sym (fn [est args] kernel-Expr))
                    syntax → term, with elaborator access via this namespace:
                      (elab est form)     elaborate a sub-form to a kernel Expr
                      (arg-type est expr) the whnf'd type of an elaborated subterm
                                          (type-directed dispatch)."
  (:require [ansatz.surface.elaborate :as elab]
            [ansatz.surface.ingest :as ingest]))

(defn elab
  "Elaborate a surface sub-form to a kernel Expr (inside a term elaborator)."
  [est form]
  (elab/elab-subterm est form))

(defn arg-type
  "The (whnf'd, zonked) kernel TYPE of an elaborated subterm Expr."
  [est expr]
  (elab/subterm-type est expr))

(defn whnf
  "whnf a kernel expr (typically a type) in the elaboration context."
  [est expr]
  (elab/subterm-whnf est expr))

(defn elab-base
  "Elaborate a form through the BUILT-IN forms (user registries bypassed for its own
   head dispatch; sub-forms dispatch normally) — delegation for wrapping elaborators."
  [est form]
  (elab/elab-base est form))

(defn with-local
  "Run (f est' fvar-id) with `sym` bound to a fresh local of kernel type `ty` —
   the narrowing primitive (rebind a variable at a refined type for one branch)."
  [est sym ty f]
  (elab/with-local est sym ty f))

(defn register-term-elaborator!
  "Register a lean4 elab_rules-shaped term elaborator: (fn [est args] → kernel Expr)."
  [sym f]
  (swap! ingest/term-elaborator-registry assoc sym f))

(defn register-keyword-access!
  "Register type-directed keyword projection for a NON-structure receiver type:
   `(:k x)` where x's type head is `type-name` calls (f est kw receiver-expr) → Expr.
   The kw arrives in full (namespace included)."
  [type-name f]
  (swap! ingest/keyword-access-registry assoc (str type-name) f))

(defn register-comparison!
  "Register type-directed 2-arg comparison for a custom scalar-carrying type: when an
   operand of `(< a b)` / `(<= a b)` / `(== a b)` has type head `type-name`, the elaborator
   calls (f est rel a-expr b-expr) → Bool Expr (rel ∈ {:lt :le :eq}) instead of the
   Nat/Int/Float/String path."
  [type-name f]
  (swap! ingest/comparison-registry assoc (str type-name) f))

(defn register-elaborator!
  "Register a lean4 macro_rules-shaped surface form: (fn [args] → surface form)."
  [sym f]
  (swap! ingest/elaborator-registry assoc sym f))
