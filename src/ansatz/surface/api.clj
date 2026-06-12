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

(defn register-term-elaborator!
  "Register a lean4 elab_rules-shaped term elaborator: (fn [est args] → kernel Expr)."
  [sym f]
  (swap! ingest/term-elaborator-registry assoc sym f))

(defn register-elaborator!
  "Register a lean4 macro_rules-shaped surface form: (fn [args] → surface form)."
  [sym f]
  (swap! ingest/elaborator-registry assoc sym f))
