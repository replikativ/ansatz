(ns ansatz.lean.jvm.original
  "Original occurrence-metadata and body-call Header borrowing checks.")
(defn- need [p message] (when-not p (throw (ex-info message {:code "ArtifactConflict"}))))
(defn direct-names [row]
  ;; Metadata edges also contain initializer/redirect associations, which are
  ;; needed for closure capture but are not body-call borrows. Read actual IR
  ;; FAP/PAP targets, then borrow each external canonical Header once.
  (let [targets (for [node (tree-seq coll? seq (get-in row ["ir" "fdecl" "body"]))
                      :when (map? node) [kind value] node :when (#{"fap" "pap"} kind)]
                  (get value "c"))
        declared (set (get row "dependencies"))]
    (need (every? declared targets) "Actual body target missing from original occurrence metadata")
    (vec (distinct (remove #(= (get row "name") %) targets)))))
