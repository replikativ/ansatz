(ns kernel-support.string-carrier
  "Read-only contextual String decoding for test constructor carriers.")
(defn- fail [message data] (throw (ex-info message data)))
(defn string-value
  "Contextual String view preserving the identity of a heap carrier."
  [ops world value]
  (if (string? value) value
    (let [node (when (and (:ref? ops) ((:ref? ops) value)) ((:node ops) world value))]
      (when-not (and (= :string (:kind node)) (string? (:text node)))
        (fail "Expected guest String carrier" {:value value}))
      (:text node))))
