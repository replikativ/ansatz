(ns ansatz.lean.jvm.type-graph
  "Private v3 logical graph model. Shape/digest checks confer no native evidence,
   layout, allocation or public entry admission authority. Existing v2 is unchanged."
  (:require [clojure.data.json :as json])
  (:import [java.nio.charset StandardCharsets] [java.security MessageDigest]))

(def limits
  {:definitions 256 :constructors 1024 :fields 64 :edges 4096
   :type-nodes 8192 :type-depth 32 :roots 1024 :arguments 64 :universes 32
   :universe 255 :name-depth 64 :name-leaf 1024 :name-units 65536
   :encoded-bytes 1048576})

(defn- need [ok reason]
  (when-not ok (throw (ex-info (str "Invalid v3 type graph: " (name reason))
                             {:code "InvalidTypeGraph" :reason reason}))))
(defn- keys! [x expected]
  (need (and (map? x) (= (count expected) (count x))
             (= expected (set (keys x)))) :keys))
(defn- bounded! [x maximum reason]
  (need (and (integer? x) (<= 0 x maximum)) reason))
(defn- vector! [x maximum reason]
  (need (and (vector? x) (<= (count x) maximum)) reason))
(defn- hex! [x]
  (need (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))) :digest))
(defn- utf16! [^String s]
  (loop [i 0]
    (when (< i (.length s))
      (let [c (.charAt s i)]
        (cond
          (Character/isHighSurrogate c)
          (do (need (and (< (inc i) (.length s))
                         (Character/isLowSurrogate (.charAt s (inc i)))) :utf16)
              (recur (+ i 2)))
          (Character/isLowSurrogate c) (need false :utf16)
          :else (recur (inc i)))))))
(defn- name! [x units nonanonymous?]
  (when nonanonymous? (need (not= ["anonymous"] x) :anonymous-name))
  (loop [x x depth 0]
    (need (< depth (:name-depth limits)) :name-depth)
    (need (vector? x) :name)
    (if (= ["anonymous"] x) true
      (do
        (need (and (= 3 (count x)) (#{"str" "num"} (nth x 0))
                   (string? (nth x 2))) :name)
        (let [leaf (nth x 2)]
          (need (<= (count leaf) (:name-leaf limits)) :name-leaf)
          (utf16! leaf)
          (need (<= (vswap! units + (count leaf)) (:name-units limits)) :name-units)
          (when (= "num" (nth x 0))
            (need (and (<= 1 (count leaf) 20)
                       (boolean (re-matches #"0|[1-9][0-9]*" leaf))
                       (<= (bigint leaf) 18446744073709551615N)) :name-number)))
        (recur (nth x 1) (inc depth))))))

(defn- children [t]
  (case (get t "kind")
    ("option" "list" "array") [(get t "element")]
    "product" [(get t "first") (get t "second")]
    "sum" [(get t "left") (get t "right")]
    "except" [(get t "error") (get t "value")]
    []))
(defn- refs [t]
  (if (= "nominal" (get t "kind")) #{(get t "id")}
    (into #{} (mapcat refs) (children t))))
(defn- definition-types [d]
  (concat (get d "arguments")
          (for [c (get d "constructors") f (get c "fields")] (get f "type"))))
(defn- index-of [g] (into {} (map #(vector (get % "id") %) (get g "definitions"))))
(defn- map-type [f t]
  (case (get t "kind")
    "nominal" (f t)
    ("option" "list" "array") (update t "element" #(map-type f %))
    "product" (-> t (update "first" #(map-type f %)) (update "second" #(map-type f %)))
    "sum" (-> t (update "left" #(map-type f %)) (update "right" #(map-type f %)))
    "except" (-> t (update "error" #(map-type f %)) (update "value" #(map-type f %)))
    t))
(defn- canonical* [g roots]
  (let [index (index-of g) numbering (volatile! {}) order (volatile! [])]
    (loop [todo (vec (reverse roots))]
      (when (seq todo)
        (let [t (peek todo) rest (pop todo)]
          (if (= "nominal" (get t "kind"))
            (let [id (get t "id")]
              (if (contains? @numbering id) (recur rest)
                (do (vswap! numbering assoc id (count @order))
                    (vswap! order conj id)
                    (recur (into rest (reverse (definition-types (get index id))))))))
            (recur (into rest (reverse (children t))))))))
      (let [rewrite #(map-type (fn [t] (assoc t "id" (get @numbering (get t "id")))) %)]
        {"schema" "lean-jvm-type-graph/3"
         "roots" (mapv rewrite roots)
         "definitions"
         (mapv (fn [id]
                 (-> (get index id)
                     (assoc "id" (get @numbering id))
                     (update "arguments" #(mapv rewrite %))
                     (update "constructors"
                             (fn [cs] (mapv #(update % "fields"
                                                    (fn [fs] (mapv (fn [f] (update f "type" rewrite)) fs))) cs)))))
               @order)})))
(defn- ordered [x]
  (cond (map? x) (into (sorted-map) (map (fn [[k v]] [k (ordered v)])) x)
        (vector? x) (mapv ordered x)
        :else x))
(defn- json-bytes [x]
  (.getBytes ^String (json/write-str (ordered x) :escape-unicode false :escape-slash false)
             StandardCharsets/UTF_8))
(defn- digest [x]
  (apply str (map #(format "%02x" (bit-and 255 %))
                  (.digest (MessageDigest/getInstance "SHA-256") (json-bytes x)))))

(defn- regular! [index]
  (let [edges (into {} (for [[id d] index]
                               [id (into #{} (mapcat refs) (definition-types d))]))
        args (into {} (for [[id d] index] [id (into #{} (mapcat refs) (get d "arguments"))]))
        order (volatile! [])]
    ;; Only constructor-field self edges are regular recursion; other cycles are
    ;; mutual/argument recursion and outside this profile.
    (doseq [id (keys index)]
      (need (not (contains? (get args id) id)) :recursive-argument))
    (loop [remaining (set (keys index)) complete #{}]
      (when (seq remaining)
        (let [ready (vec (sort (filter #(every? complete (disj (get edges %) %)) remaining)))]
          (need (seq ready) :nonregular-cycle)
          (vswap! order into ready)
          (recur (reduce disj remaining ready) (into complete ready)))))
    (letfn [(closure [seed]
              (loop [todo (vec seed) seen #{}]
                (if (empty? todo) seen
                  (let [id (peek todo) rest (pop todo)]
                    (if (contains? seen id) (recur rest seen)
                      (recur (into rest (get edges id)) (conj seen id)))))))
            (family [id] (let [d (get index id)] [(get d "origin") (get d "name")]))]
      (doseq [id (keys index)
              :let [argument-closure (closure (get args id))]
              other (disj (closure (get edges id)) id)]
        (when (= (family id) (family other))
          (need (contains? argument-closure other) :changed-recursive-application))))
    ;; Closed application identity follows argument dependencies only. Memoized
    ;; hashes avoid expanding shared/nested application arguments exponentially.
    (let [cache (volatile! {})]
      (doseq [id @order]
        (let [d (get index id)
              key (digest [(get d "origin") (get d "name") (get d "universes")
                           (mapv #(map-type (fn [t] {"kind" "closed-application"
                                                    "digest" (get @cache (get t "id"))}) %)
                                 (get d "arguments"))])]
          (vswap! cache assoc id key)))
      (need (= (count @cache) (count (set (vals @cache)))) :duplicate-application))))

(defn validate!
  "Strict bounded logical model check; return the input unchanged. This does not
   prove declaration safety, native DefEq, origin authenticity or actual layout."
  [g]
  (keys! g #{"schema" "roots" "definitions"})
  (need (= "lean-jvm-type-graph/3" (get g "schema")) :schema)
  (vector! (get g "roots") (:roots limits) :roots)
  (need (seq (get g "roots")) :roots)
  (vector! (get g "definitions") (:definitions limits) :definitions)
  (let [units (volatile! 0) nodes (volatile! 0) edges (volatile! 0)
        constructors (volatile! 0) ids (volatile! #{})]
    (letfn [(type! [t depth]
              (need (< depth (:type-depth limits)) :type-depth)
              (need (<= (vswap! nodes inc) (:type-nodes limits)) :type-nodes)
              (need (map? t) :type)
              (let [kind (get t "kind")]
                (need (and (string? kind) (<= (count kind) 16)) :unsupported-type)
                (case kind
                  ("nat" "int" "bool" "string" "unit" "char" "bytes") (keys! t #{"kind"})
                  "nominal" (do (keys! t #{"kind" "id"})
                                (bounded! (get t "id") (dec (:definitions limits)) :id)
                                (need (contains? @ids (get t "id")) :missing-reference))
                  "machine-int" (do (keys! t #{"kind" "bits" "signed"})
                                    (bounded! (get t "bits") 64 :scalar)
                                    (need (and (#{8 16 32 64} (get t "bits"))
                                               (instance? Boolean (get t "signed"))) :scalar))
                  "word" (do (keys! t #{"kind" "signed"})
                             (need (instance? Boolean (get t "signed")) :scalar))
                  "float" (do (keys! t #{"kind" "bits"})
                              (bounded! (get t "bits") 64 :scalar)
                              (need (#{32 64} (get t "bits")) :scalar))
                  ("option" "list" "array") (keys! t #{"kind" "element"})
                  "product" (keys! t #{"kind" "first" "second"})
                  "sum" (keys! t #{"kind" "left" "right"})
                  "except" (keys! t #{"kind" "error" "value"})
                  (need false :unsupported-type))
                (doseq [child (children t)]
                  (need (<= (vswap! edges inc) (:edges limits)) :edges)
                  (type! child (inc depth)))
                (when (= "nominal" kind)
                  (need (<= (vswap! edges inc) (:edges limits)) :edges))))]
      (doseq [d (get g "definitions")]
        (keys! d #{"id" "origin" "name" "universes" "arguments" "constructors"})
        (bounded! (get d "id") (dec (:definitions limits)) :id)
        (need (not (contains? @ids (get d "id"))) :duplicate-id)
        (vswap! ids conj (get d "id")))
      (doseq [d (get g "definitions")]
        (keys! (get d "origin") #{"module" "productSha256"})
        (name! (get-in d ["origin" "module"]) units true)
        (hex! (get-in d ["origin" "productSha256"]))
        (name! (get d "name") units true)
        (vector! (get d "universes") (:universes limits) :universes)
        (doseq [u (get d "universes")] (bounded! u (:universe limits) :universe))
        (vector! (get d "arguments") (:arguments limits) :arguments)
        (doseq [t (get d "arguments")] (type! t 0))
        (vector! (get d "constructors") (:constructors limits) :constructors)
        (need (seq (get d "constructors")) :constructors)
        (doseq [c (get d "constructors")]
          (need (<= (vswap! constructors inc) (:constructors limits)) :constructors)
          (keys! c #{"name" "fields"})
          (name! (get c "name") units true)
          (vector! (get c "fields") (:fields limits) :fields)
          (doseq [f (get c "fields")]
            (keys! f #{"name" "type"})
            (name! (get f "name") units false)
            (type! (get f "type") 0)))
        (let [names (mapv #(get % "name") (get d "constructors"))]
          (need (= (count names) (count (set names))) :duplicate-constructor)))
      (doseq [t (get g "roots")] (type! t 0))
      (need (= (count (get g "roots")) (count (set (get g "roots")))) :duplicate-root)
      (regular! (index-of g))
      (let [canonical (canonical* g (get g "roots"))]
        (need (= (count @ids) (count (get canonical "definitions"))) :unreachable-definition)
        (need (<= (alength ^bytes (json-bytes canonical)) (:encoded-bytes limits)) :encoded-bytes))))
  g)

(defn canonical-graph
  "Canonical rooted traversal renumbers local IDs; root/constructor/field order
   remains significant. Definition table order and original IDs do not."
  [g] (validate! g) (canonical* g (get g "roots")))
(defn logical-digest
  "SHA-256 of canonical UTF-8 JSON. Binds this whole evidence graph, including
   ordered roots; this is NOT a nominal type's identity digest."
  [g] (digest (canonical-graph g)))
(defn type-digest
  "Digest only one validated closed type's reachable closure. Unrelated selected
   roots/definitions do not affect it. Accept a graph root or declared nominal."
  [g t]
  (validate! g)
  (need (or (some #(= t %) (get g "roots"))
            (and (map? t) (= #{"kind" "id"} (set (keys t)))
                 (= "nominal" (get t "kind")) (contains? (index-of g) (get t "id")))) :not-root)
  (digest (canonical* g [t])))

(defn validate-layout-references!
  "Check reference paths into a separately authenticated representation document.
   Does NOT validate that document, its digest, native field correspondence or
   offsets; callers receive no allocation/read authority from this function."
  [g plan]
  (validate! g)
  (keys! plan #{"schema" "logicalDigest" "representationDigest" "definitions"})
  (need (= "lean-jvm-layout-references/3" (get plan "schema")) :layout-schema)
  (hex! (get plan "logicalDigest"))
  (hex! (get plan "representationDigest"))
  (need (= (logical-digest g) (get plan "logicalDigest")) :logical-digest)
  (let [index (index-of (canonical-graph g)) ds (get plan "definitions")]
    (vector! ds (:definitions limits) :layout-definitions)
    (doseq [d ds]
      (keys! d #{"definition" "applicationPath" "constructors"})
      (bounded! (get d "definition") (dec (:definitions limits)) :id))
    (need (= (set (keys index)) (set (map #(get % "definition") ds))) :layout-closure)
    (need (= (count index) (count ds)) :layout-duplicates)
    (doseq [d ds]
      (keys! d #{"definition" "applicationPath" "constructors"})
      (bounded! (get d "definition") (dec (:definitions limits)) :id)
      (let [ap (get d "applicationPath")
            cs (get d "constructors")
            logical (get-in index [(get d "definition") "constructors"])]
        (need (and (vector? ap) (= 2 (count ap)) (= "applications" (first ap))) :application-path)
        (bounded! (second ap) (dec (:definitions limits)) :application-path)
        (vector! cs (:constructors limits) :layout-constructors)
        (need (= (vec (range (count logical))) (mapv #(get % "constructor") cs)) :layout-constructor-order)
        (doseq [[i c] (map-indexed vector cs)]
          (keys! c #{"constructor" "layoutPath" "fields"})
          (let [p (get c "layoutPath") fs (get c "fields")]
            (need (and (vector? p) (= 4 (count p)) (= "families" (nth p 0))
                       (= "constructors" (nth p 2))) :constructor-path)
            (bounded! (nth p 1) (dec (:definitions limits)) :constructor-path)
            (bounded! (nth p 3) (dec (count logical)) :constructor-path)
            (vector! fs (:fields limits) :layout-fields)
            (need (= (vec (range (count (get (nth logical i) "fields"))))
                     (mapv #(get % "field") fs)) :layout-field-order)
            (doseq [f fs]
              (keys! f #{"field" "layoutPath"})
              (let [fp (get f "layoutPath")]
                (need (and (vector? fp) (= 6 (count fp)) (= p (subvec fp 0 4))
                           (= "fields" (nth fp 4))) :field-path)
                (bounded! (nth fp 5) (dec (:fields limits)) :field-path)))
            (need (= (count fs) (count (set (map #(get % "layoutPath") fs)))) :duplicate-field-path))))))
  plan)
