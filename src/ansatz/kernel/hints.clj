(ns ansatz.kernel.hints
  "Exact Lean reducibility hints with the full UInt32 regular-height range.
   Legacy integer wire values keep -1=opaque, 0=abbrev, positive=regular.
   Newly representable heights use {:regular UInt32}, so old decoders fail
   explicitly rather than misreading regular(0) as abbrev."
  (:import [ansatz.kernel ConstantInfo]))

(defn code [hints]
  (cond
    (= :opaque hints) ConstantInfo/REDUCIBILITY_OPAQUE
    (= :abbrev hints) ConstantInfo/REDUCIBILITY_ABBREV
    (and (map? hints) (= #{:regular} (set (keys hints))))
    (let [h (:regular hints)]
      (when-not (and (integer? h) (<= 0 h ConstantInfo/MAX_REGULAR_HEIGHT))
        (throw (ex-info "Regular reducibility height must fit UInt32" {:hints hints})))
      (long h))
    :else (throw (ex-info "Invalid reducibility hints" {:hints hints}))))

(defn symbolic [^ConstantInfo ci]
  (let [h (.getHintsCode ci)]
    (cond (= h ConstantInfo/REDUCIBILITY_OPAQUE) :opaque
          (= h ConstantInfo/REDUCIBILITY_ABBREV) :abbrev
          :else {:regular h})))

(defn wire-value [^ConstantInfo ci]
  (if (= (.getHints ci) ConstantInfo/HINTS_EXTENDED)
    (symbolic ci)
    (.getHints ci)))

(defn wire-code [value]
  (if (integer? value)
    (cond (= value -1) ConstantInfo/REDUCIBILITY_OPAQUE
          (= value 0) ConstantInfo/REDUCIBILITY_ABBREV
          (<= 1 value Integer/MAX_VALUE) (long value)
          :else (throw (ex-info "Invalid legacy reducibility hints" {:hints value})))
    (code value)))
