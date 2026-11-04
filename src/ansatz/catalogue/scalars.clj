(ns ansatz.catalogue.scalars
  "Dependency-free conversion of store artifacts into catalogue scalar entities."
  (:require [ansatz.simp-index :as si]))

(defn scalar-entities
  "One entity map per declaration name from every source, scalars only (refs come second, once
   the entities exist), in declaration order."
  [{:keys [recall-keys simp-keys facts modules attrs instances]}]
  ;; DECLARATION ORDER, deliberately: entities are transacted in this order, so their ids are
  ;; contiguous per facts chunk, so each chunk's ref batch touches a contiguous range of the
  ;; entity-sorted indices instead of every leaf (HashMap order scattered the ids and each
  ;; 500k-datom commit rewrote the whole tree: 15 GB of superseded nodes for Mathlib).
  (let [by-name (java.util.LinkedHashMap.)
        ent! (fn [n f] (.put by-name n (f (or (.get by-name n) {:decl/name n}))))]
    (doseq [f facts]
      (ent! (:name f) #(cond-> (assoc % :decl/kind (:kind f) :decl/num-univs (:num-univs f)
                                      :decl/num-binders (:num-binders f) :decl/type-id (:type-id f))
                         (:concl-head f) (assoc :decl/concl-head (:concl-head f))
                         (:value-id f) (assoc :decl/value-id (:value-id f)))))
    (doseq [[n k] recall-keys] (ent! n #(assoc % :decl/dt-key k)))
    (doseq [[n k] (si/key-entries simp-keys)] (ent! n #(update % :decl/simp-key (fnil conj #{}) k)))
    (doseq [[n {:keys [module doc]}] modules :when (.containsKey by-name n)]
      (ent! n #(cond-> (assoc % :decl/module module) doc (assoc :decl/doc doc))))
    (doseq [[kind n _ prio] attrs]
      (ent! n #(cond-> (update % :decl/attr (fnil conj #{}) kind)
                 (and (= kind "simp") prio) (assoc :decl/simp-prio prio))))
    (doseq [[_ insts] instances {:keys [name priority]} insts]
      (ent! (str name) #(cond-> (update % :decl/attr (fnil conj #{}) "instance")
                          priority (assoc :decl/instance-prio priority))))
    (vec (.values by-name))))
