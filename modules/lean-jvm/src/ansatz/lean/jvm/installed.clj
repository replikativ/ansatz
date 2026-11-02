(ns ansatz.lean.jvm.installed
  "Pure finite installed-product provenance. No native services or filesystem IO."
  (:require [clojure.string :as str]))

(def profile "explicit-installed-imports/1")
(def preparation-profile "native-local-installed-project-prepare/1")
(def artifact-profile "legacy-local-installed-v1")
(def max-modules 128)
(def max-product-bytes (* 64 1048576))
(def max-total-bytes (* 256 1048576))
(def suffixes [".olean" ".olean.server" ".olean.private" ".ir.sig" ".ir"])
(defn- need [ok facts]
  (when-not ok (throw (ex-info "Invalid installed import provenance" (assoc facts :code "ArtifactConflict")))))
(defn components [name]
  (loop [n name parts [] total 0]
    (need (and (vector? n) (< (count parts) 65) (<= total 4096)) {:module name})
    (if (= n ["anonymous"])
      (do (need (seq parts) {:module name}) (vec (reverse parts)))
      (do
        (need (and (= 3 (count n)) (= "str" (first n))) {:module name})
        (let [s (nth n 2)]
          (need (and (string? s) (<= 1 (count s) 255)
                     (not (#{"." ".." ".lake" ".git" "build"} s))
                     (not-any? #(or (= % \/) (= % \\) (zero? (int %))) s)) {:module name})
          (recur (second n) (conj parts s) (+ total (count s))))))))
(defn init? [name] (= "Init" (first (components name))))
(defn product-paths [name]
  (let [stem (str/join "/" (components name))] (mapv #(str stem %) suffixes)))
(defn declared! [names]
  (need (and (vector? names) (<= (count names) max-modules) (= (count names) (count (set names)))) {})
  (doseq [name names] (need (not (init? name)) {:module name :reason :init-is-implicit})) names)
(defn validate! [snapshot]
  (need (and (map? snapshot) (= #{"profile" "modules"} (set (keys snapshot)))
             (= profile (get snapshot "profile")) (vector? (get snapshot "modules"))
             (<= 1 (count (get snapshot "modules")) max-modules)) {})
  (declared! (mapv #(get % "module") (get snapshot "modules")))
  (let [total (volatile! 0)]
    (doseq [module (get snapshot "modules")]
      (need (= #{"module" "products"} (set (keys module))) {})
      (let [products (get module "products")]
        (need (and (vector? products) (= (product-paths (get module "module")) (mapv #(get % "path") products))
                   (true? (get-in products [0 "present"]))) {:module (get module "module")})
        (doseq [product products]
          (let [present (get product "present") bytes (get product "bytes") sha (get product "sha256")]
            (need (and (boolean? present)
                       (= (if present #{"path" "present" "bytes" "sha256"} #{"path" "present"}) (set (keys product)))
                       (or (not present) (and (integer? bytes) (<= 0 bytes max-product-bytes)
                                             (string? sha) (re-matches #"[0-9a-f]{64}" sha)))) {:product product})
            (when present (vswap! total + bytes))))))
    (need (<= @total max-total-bytes) {:reason :product-byte-limit})) snapshot)
(defn validate-graph!
  "Every actual effective module and declaration owner must be local, Init, or
   explicitly declared. Product identity does not relax initialization admission."
  [snapshot locals orders rows]
  (validate! snapshot)
  (let [allowed (into (set locals) (map #(get % "module") (get snapshot "modules")))
        allowed? #(or (contains? allowed %) (and % (init? %)))]
    (doseq [order orders]
      (need (and (vector? order) (<= (count order) 4096)) {})
      (doseq [module order] (need (allowed? module) {:module module :reason :undeclared-import})))
    (doseq [row rows]
      (need (allowed? (get row "sourceModule")) {:name (get row "name") :reason :undeclared-owner}))) true)
