(ns java-ir-scope-cache-model
  "Independent conceptual stack-of-scope-maps oracle. Values are integer tokens;
   this does not duplicate the runtime's generation-linked per-key stacks or RC.")
(defn initial [] {:scopes [{}] :watermark 0})
(defn command [state row]
  (let [op (first row) depth (dec (count (:scopes state))) key [(nth row 1 nil) (nth row 2 nil)]]
    (case op
      0 [(update state :scopes conj {}) nil nil]
      1 [(update state :scopes pop) nil nil]
      2 (if-let [entry (get (peek (:scopes state)) key)]
          [(update state :watermark max (:scope entry)) (:value entry) true]
          [state nil false])
      3 (let [computed (row 3) result-scope (row 4)
              ;; Conceptual entries occupy their valid scope interval. The most
              ;; local surviving entry decides whether old sharing is reused.
              top (some #(get % key) (rseq (:scopes state)))
              selected (if (= result-scope (:scope top)) (:value top) computed)
              entry {:value selected :scope result-scope}
              scopes (reduce #(assoc-in %1 [%2 key] entry) (:scopes state) (range result-scope (inc depth)))]
          [(assoc state :scopes scopes) selected nil]))))
