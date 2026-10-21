(ns prototype.preparation
  "Explicit trusted preparation of a closed executable graph. No execution,
   initializer replay, provenance inference or replacement of existing code."
  (:require [prototype.import-ir :as ir]
            [prototype.eval-const :as eval]
            [prototype.machine :as m]))

(defn complete-functions
  "Walk actual existing bodies, linking only absent targets from CATALOGUE using
   LOWER and the ordinary trusted linker. Preserve every existing object identity.
   Capture executable authority only after this preparation succeeds. Missing
   synthetic wrappers are errors unless the trusted linker can actually supply
   them; names are never guessed or silently skipped. This returns code only."
  [catalogue functions roots lower]
  (when-not (and (map? functions) (or (sequential? roots) (set? roots)))
    (m/fail "Invalid trusted preparation inputs" {}))
  (loop [functions functions pending (vec roots) seen #{}]
    (if (empty? pending) functions
        (let [name (peek pending) pending (pop pending)]
          (when (nil? name) (m/fail "Malformed executable root" {}))
          (if (contains? seen name) (recur functions pending seen)
              (let [functions (if (contains? functions name) functions
                                  (ir/load-closure catalogue [name] lower {:existing-functions functions}))
                    function (get functions name)]
                (when-not (map? function) (m/fail "Missing prepared executable" {:name name}))
                (recur functions (into pending (eval/executable-dependencies function)) (conj seen name))))))))
