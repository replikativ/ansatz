(ns kernel-support.constructor-layout
  "Pinned 64-bit constructor storage admission. A raw-clone descriptor witnesses only
   an allocation's validated physical scalar extent; it is NOT native source,
   object, kernel-certificate, or file identity. Guest IR cannot construct this
   host metadata. Values remain checked against their current bytes/layout.")
(defn- byte?* [x] (and (integer? x) (<= 0 x 255)))
(defn- physical-storage? [node objects extent]
  (and (= :ctor (:kind node)) (= objects (count (:fields node)))
       (integer? objects) (<= 0 objects 255)
       (integer? extent) (<= 0 extent 1023) (zero? (rem extent 8))
       (= (when (pos? extent) {:objects objects :usize 0 :ssize extent}) (:layout node))
       (map? (:scalar-bytes node))
       (= extent (count (:scalar-bytes node)))
       (every? #(byte?* (get (:scalar-bytes node) (+ (* 8 objects) %))) (range extent))))
(defn clone-storage
  "Attach a witness only after checking a complete normalized physical clone.
   Does not copy or manufacture any :native-source-id/:native-object-bytes."
  [node]
  (let [objects (count (:fields node)) extent (get-in node [:layout :ssize] 0)]
    (when-not (physical-storage? node objects extent)
      (throw (ex-info "Invalid raw cloned constructor storage" {})))
    (assoc node :raw-clone-layout {:profile :lean64-align8-v1 :objects objects :scalar-size extent})))
(defn physical-layout?
  "Native-import or validated clone storage, with exact expected physical extent.
   This grants storage-layout admission only, never NativeSource membership."
  [node objects semantic-size]
  (let [padded (* 8 (quot (+ semantic-size 7) 8)) witness (:raw-clone-layout node)]
    (or (and (integer? (:native-source-id node)) (<= 0 (:native-source-id node))
             (= (+ 8 (* 8 objects) padded) (:native-object-bytes node)))
        (and (map? witness) (= #{:profile :objects :scalar-size} (set (keys witness)))
             (= :lean64-align8-v1 (:profile witness)) (= objects (:objects witness))
             (= padded (:scalar-size witness)) (physical-storage? node objects padded)))))
(defn constructor-layout? [node objects semantic-size]
  (let [layout (:layout node) padded (* 8 (quot (+ semantic-size 7) 8))
        physical? (physical-layout? node objects semantic-size)
        extent (if (and physical? (pos? semantic-size)) padded semantic-size)]
    (and (= :ctor (:kind node)) (= objects (count (:fields node)))
         (if (zero? semantic-size)
           (and (nil? layout) (empty? (:scalar-bytes node)))
           (and (or (= {:objects objects :usize 0 :ssize semantic-size} layout)
                    (and physical? (= {:objects objects :usize 0 :ssize padded} layout)))
                (every? #(byte?* (get (:scalar-bytes node) (+ (* 8 objects) %))) (range extent)))))))
