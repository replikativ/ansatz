(ns ansatz.lean.jvm.used-products
  "Private pure v3 used-origin product model. Validation establishes shape and
   internal correspondence only; the source issuer must capture/recheck bytes.
   A caller-created manifest never grants native or public entry authority."
  (:require [ansatz.lean.jvm.installed :as installed]
            [ansatz.lean.jvm.type-graph :as graph]
            [clojure.data.json :as json])
  (:import [java.nio.charset StandardCharsets] [java.security MessageDigest]))

(def schema "lean-jvm-used-module-products/1")
(def max-modules 256)
(def max-encoded-bytes (* 4 1048576))

(defn- need [ok reason]
  (when-not ok
    (throw (ex-info "Invalid used-module product provenance"
                    {:code "InvalidUsedModuleProducts" :reason reason}))))
(defn- exact! [x ks]
  (need (and (map? x) (= ks (set (keys x)))) :keys))
(defn- sha! [x]
  (need (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))) :digest))
(defn- module! [x]
  ;; Reuse the actual installed-module path grammar, including traversal guards.
  (try (installed/components x)
       (catch clojure.lang.ExceptionInfo _ (need false :module)))
  (loop [n x]
    (when-not (= ["anonymous"] n)
      (let [^String text (nth n 2)]
        (loop [i 0]
          (when (< i (.length text))
            (let [c (.charAt text i)]
              (cond
                (Character/isHighSurrogate c)
                (do (need (and (< (inc i) (.length text))
                               (Character/isLowSurrogate (.charAt text (inc i)))) :module-utf16)
                    (recur (+ i 2)))
                (Character/isLowSurrogate c) (need false :module-utf16)
                :else (recur (inc i)))))))
      (recur (second n))))
  x)

(defn validate!
  "Check exact pathless roles and primary-product identity, including absence.
   Empty manifests are valid for signatures containing only builtin types."
  [document]
  (exact! document #{"schema" "modules"})
  (need (= schema (get document "schema")) :schema)
  (let [modules (get document "modules") total (volatile! 0)]
    (need (and (vector? modules) (<= (count modules) max-modules)) :modules)
    (need (= (count modules) (count (set (map #(get % "module") modules)))) :duplicate-module)
    (doseq [m modules]
      (exact! m #{"module" "productSha256" "products"})
      (module! (get m "module"))
      (sha! (get m "productSha256"))
      (let [products (get m "products")]
        (need (and (vector? products)
                   (= installed/suffixes (mapv #(get % "role") products))) :roles)
        (doseq [p products]
          (let [present (get p "present")]
            (need (boolean? present) :presence)
            (exact! p (if present #{"role" "present" "bytes" "sha256"} #{"role" "present"}))
            (when present
              (let [bytes (get p "bytes")]
                (need (and (integer? bytes) (<= 0 bytes installed/max-product-bytes)) :product-bytes)
                (sha! (get p "sha256"))
                (need (<= (vswap! total + bytes) installed/max-total-bytes) :total-bytes)))))
        (need (true? (get-in products [0 "present"])) :primary-missing)
        (need (= (get m "productSha256") (get-in products [0 "sha256"])) :primary-digest))))
  document)

(defn authorize!
  "Require the complete batch inventory, local origins or explicitly allowed
   installed origins. Used-origin inventory itself cannot authorize imports."
  [document required-modules local-modules declared-installed]
  (validate! document)
  (doseq [names [required-modules local-modules declared-installed]]
    (need (and (vector? names) (<= (count names) max-modules)
               (= (count names) (count (set names)))) :module-set)
    (doseq [n names] (module! n)))
  (let [actual (set (map #(get % "module") (get document "modules")))
        locals (set local-modules) declared (set declared-installed)]
    (need (= actual (set required-modules)) :inventory-mismatch)
    (need (not-any? declared locals) :origin-shadowing)
    (need (not-any? installed/init? (concat local-modules declared-installed)) :init-shadowing)
    (doseq [n actual]
      (need (or (contains? locals n) (contains? declared n) (installed/init? n)) :undeclared-origin)))
  document)

(defn bind-graph!
  "Bind every logical definition to its actual defining primary product and
   reject unused products. Does not authenticate the supplied product bytes."
  [document logical]
  (validate! document)
  (graph/validate! logical)
  (let [origins (mapv #(get % "origin") (get logical "definitions"))
        products (into {} (map #(vector (get % "module") (get % "productSha256"))
                               (get document "modules")))]
    (need (= (set (keys products)) (set (map #(get % "module") origins))) :graph-origin-set)
    (doseq [origin origins]
      (need (= (get products (get origin "module")) (get origin "productSha256")) :graph-product)))
  document)

(defn- canonical-value [x]
  (cond (map? x) (into (sorted-map) (map (fn [[k v]] [k (canonical-value v)])) x)
        (vector? x) (mapv canonical-value x)
        :else x))

(defn canonical-bytes
  "Order-independent module-set encoding, with exact role order preserved."
  [document]
  (validate! document)
  (let [ordered (update document "modules"
                        #(vec (sort-by (fn [m] (json/write-str (get m "module")
                                                             :escape-unicode false :escape-slash false)) %)))
        bytes (.getBytes (json/write-str (canonical-value ordered)
                                       :escape-unicode false :escape-slash false) StandardCharsets/UTF_8)]
    (need (<= (alength bytes) max-encoded-bytes) :encoded-bytes)
    bytes))

(defn digest [document]
  (let [bytes (.digest (MessageDigest/getInstance "SHA-256") (canonical-bytes document))]
    (apply str (map #(format "%02x" (bit-and 255 %)) bytes))))
