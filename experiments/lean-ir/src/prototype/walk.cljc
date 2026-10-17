(ns prototype.walk
  "Stack-safe traversal of deeply nested compiler forms.")

(defn forms
  "Lazy depth-first preorder traversal, including ROOT and collection nodes.
   Has tree-seq coll?/seq order without recursive lazy concat realization."
  [root]
  (letfn [(step [pending]
            (lazy-seq
             (loop [pending pending]
               (when (seq pending)
                 (if-let [siblings (seq (peek pending))]
                   (let [value (first siblings)
                         pending (conj (pop pending) (rest siblings))
                         pending (if (coll? value) (conj pending (seq value)) pending)]
                     (cons value (step pending)))
                   (recur (pop pending)))))))]
    (step [(list root)])))
