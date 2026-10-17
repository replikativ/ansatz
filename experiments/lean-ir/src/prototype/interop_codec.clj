(ns prototype.interop-codec
  "Explicit typed values for the pinned Lean guest ABI; no signature inference.
   Raw scalar descriptors denote unboxed IR values at the call boundary.
   Constructor fields (Option/IO) box UInt64/USize/Float/Float32 as Lean does.
   Option host values are nil(None) or {:some value}, preserving Some Unit.
   Unit/world host values are nil; the world guest value is m/erased.
   Decode borrows all guest values. The caller retains ownership of its world
   and result, including error objects reported by [:io kind]. Native immediate
   words are contextualized only on decode. Imported/cloned scalar padding requires
   a validated physical-storage witness; host encode inputs keep their explicit types."
  (:require [prototype.machine :as m]
            [prototype.scalar :as scalar]
            [prototype.constructor-layout :as constructor]
            [prototype.native-scalar :as native]
            [prototype.kernel-bridge :as kernel]
            [prototype.runtime-string :as string]))

(def ^:private scalars
  {:uint8 "uint8" :uint16 "uint16" :uint32 "uint32" :uint64 "uint64"
   :usize "usize" :float "float" :float32 "float32"})
(def ^:private atoms (into #{:nat :string :bytes :bool :unit :world} (keys scalars)))
(defn- fail [message data] (throw (ex-info message data)))

(defn- descriptor! [descriptor encode?]
  (cond
    (contains? atoms descriptor) descriptor
    (and (vector? descriptor) (= 2 (count descriptor))
         (contains? #{:option :io} (first descriptor)))
    (do (when (and encode? (= :io (first descriptor)))
          (fail "IO codec is decode-only" {:descriptor descriptor}))
        (descriptor! (second descriptor) encode?) descriptor)
    :else (fail "Unsupported interop descriptor" {:descriptor descriptor})))

(defn- nat! [value]
  (when-not (and (integer? value) (<= 0 value))
    (fail "Expected exact nonnegative interop Nat" {:value value})) value)
(defn- string! [value]
  (string/evaluate {} nil "lean_string_utf8_byte_size" [value]) value)
(defn- bytes! [value]
  (when-not (vector? value) (fail "Expected immutable UInt8 vector" {}))
  (mapv #(scalar/integer! "uint8" %) value))
(defn- immediate [value]
  (cond (native/native-scalar? value) (native/payload value)
        (instance? prototype.machine.Tag value) (:tag value)
        :else value))
(def ^:private carrier-ops {:ref? m/ref? :node m/node})
(defn- float-value [type value]
  ;; Never use float-number: it may quiet/canonicalize a stored NaN payload.
  (scalar/float-from-bytes type (scalar/float-bytes type value)))

(defn- constructor! [world value tags]
  (when-not (m/ref? value) (fail "Expected interop constructor reference" {:value value}))
  (let [{:keys [kind tag fields layout scalar-bytes] :as node} (m/node world value)]
    (when-not (and (= :ctor kind) (contains? tags tag) (vector? fields) (= 1 (count fields))
                   (or (nil? layout) (= {:objects 1 :usize 0 :ssize 0} layout))
                   (empty? scalar-bytes))
      (fail "Invalid interop constructor layout" {:value value :tag tag})) node))

(declare encode-value decode-value)
(defn- encode-field [world descriptor value]
  (let [[world value] (encode-value world descriptor value)]
    (if-let [type (get scalars descriptor)]
      (m/box-value world type value) [world value])))
(defn- decode-field [world descriptor value]
  (decode-value world descriptor
                (if-let [type (get scalars descriptor)]
                  (do
                    (when-let [layout (scalar/box-layout type)]
                      (when-not (m/ref? value)
                        (fail "Expected boxed interop scalar" {:descriptor descriptor}))
                      (let [node (m/node world value)]
                        (when-not (and (= :ctor (:kind node)) (= 0 (:tag node))
                                       (= [] (:fields node))
                                       (or (= layout (:layout node))
                                           (and (kernel/constructor-layout? node 0 (scalar/width type))
                                                (or (not= type "usize")
                                                    (constructor/physical-layout? node 0 (scalar/width type)))))
                                       (map? (:scalar-bytes node))
                                       (= (set (range (+ (* 8 (get-in node [:layout :usize]))
                                                        (get-in node [:layout :ssize]))))
                                          (set (keys (:scalar-bytes node)))))
                          (fail "Invalid boxed interop scalar layout" {:descriptor descriptor}))
                        (doseq [byte (vals (:scalar-bytes node))]
                          (scalar/integer! "uint8" byte))))
                    (m/unbox-value world type value)) value)))

(defn- encode-value [world descriptor value]
  (cond
    (contains? scalars descriptor)
    (let [type (get scalars descriptor)]
      [world (if (scalar/float-type? type) (float-value type value) (scalar/integer! type value))])
    (vector? descriptor)
    (if (nil? value) [world 0]
      (do (when-not (and (map? value) (= #{:some} (set (keys value))))
            (fail "Expected nil or {:some value} for Option" {:descriptor descriptor}))
          (let [[world field] (encode-field world (second descriptor) (:some value))]
            (m/allocate world :ctor 1 [field]))))
    :else
    (case descriptor
      :nat [world (nat! value)]
      :string [world (string! value)]
      :bytes (let [bytes (bytes! value)
                   [world ref] (m/allocate world :byte-array 248 [])]
               [(assoc-in world [:heap (:id ref) :bytes] bytes) ref])
      :bool (do (when-not (or (true? value) (false? value))
                  (fail "Expected host Boolean" {:value value})) [world (if value 1 0)])
      :unit (do (when-not (nil? value) (fail "Expected nil host Unit" {:value value})) [world 0])
      :world (do (when-not (nil? value) (fail "Expected nil host world token" {})) [world m/erased]))))

(defn- decode-value [world descriptor value]
  (cond
    (contains? scalars descriptor)
    (let [type (get scalars descriptor)]
      (if (scalar/float-type? type) (float-value type value) (scalar/integer! type value)))
    (vector? descriptor)
    (let [[kind child] descriptor]
      (if (and (= :option kind) (= 0 (immediate value))) nil
        (let [{:keys [tag fields]} (constructor! world value (if (= :io kind) #{0 1} #{1}))
              field (first fields)]
          (if (= :option kind) {:some (decode-field world child field)}
            (if (= 0 tag) (decode-field world child field)
              (fail "Lean IO returned an error" {:type :guest-error :guest-error field
                                                 :descriptor descriptor}))))))
    :else
    (case descriptor
      :nat (native/nat-value carrier-ops world value)
      :string (string! (string/string-value carrier-ops world value))
      :bytes (do (when-not (m/ref? value) (fail "Expected guest ByteArray reference" {:value value}))
                 (let [{:keys [kind tag fields bytes]} (m/node world value)]
                   (when-not (and (= :byte-array kind) (= 248 tag) (vector? fields) (empty? fields))
                     (fail "Invalid guest ByteArray layout" {:value value}))
                   (bytes! bytes)))
      :bool (let [value (immediate value)]
              (cond (= 0 value) false (= 1 value) true
                    :else (fail "Invalid guest Bool" {:value value})))
      :unit (do (when-not (= 0 (immediate value)) (fail "Invalid guest Unit" {:value value})) nil)
      :world (do (when-not (= m/erased value) (fail "Invalid erased world token" {})) nil))))

(defn encode
  "Return [new-world guest-value]. Newly allocated objects have one owner;
   enclosing constructors take ownership of their encoded fields."
  [world descriptor host-value]
  (descriptor! descriptor true)
  (encode-value world descriptor host-value))

(defn decode
  "Borrow guest-value and return its explicit host representation. IO errors
   throw ExceptionInfo with :type :guest-error and the owned guest error value;
   the caller's world remains the authority for inspecting/releasing that value."
  [world descriptor guest-value]
  (descriptor! descriptor false)
  (decode-value world descriptor guest-value))
