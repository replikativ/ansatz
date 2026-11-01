(ns ansatz.lean.jvm.publisher
  "Combined program publisher over actual native build receipts. No process launch."
  (:require [ansatz.lean.jvm.startup :as startup]
            [clojure.string :as str]))
(defn- need [p message] (when-not p (throw (ex-info message {:profile :ansatz.lean.jvm.publisher}))))
(defn- vector! [value limit]
  (need (and (vector? value) (<= (count value) limit)) "Bounded immutable vector required") value)
(defn- name-label [n]
  (#'startup/name! n)
  (loop [n n parts ()]
    (if (= n ["anonymous"]) (str/join "." parts)
        (recur (second n) (conj parts (nth n 2))))))
(defn- bounded-rows! [rows]
  ;; This precedes recursive JSON digest/Header construction. The BuildReceipt
  ;; already authenticated bytes; this is a runtime resource-profile guard.
  (loop [pending (mapv #(vector % 0) rows) visited 0 characters 0]
    (need (and (<= (count pending) 65536) (<= visited 2000000) (<= characters 33554432)) "Prepared source data exceeds budget")
    (when (seq pending)
      (let [[value depth] (peek pending) pending (pop pending)]
        (need (<= depth 256) "Prepared source data exceeds nesting limit")
        (cond
          (map? value) (recur (into pending (map #(vector % (inc depth)) (mapcat identity value))) (inc visited) characters)
          (vector? value) (recur (into pending (map #(vector % (inc depth)) value)) (inc visited) characters)
          (string? value) (do (need (<= (count value) 2097152) "Prepared source scalar exceeds budget")
                              (recur pending (inc visited) (+ characters (count value))))
          :else (do (need (or (nil? value) (boolean? value) (integer? value)) "Unsupported producer data carrier")
                    (recur pending (inc visited) characters)))))))
(defn- startup-observation! [selected original]
  (let [keys ["kind" "name" "ir" "dependencies" "redirect" "sourceModule"]
        expected-role (get-in original ["runtime" "role"]) selected-role (get-in selected ["runtime" "role"])]
    (need (and selected (= (select-keys selected keys) (select-keys original keys))
               (= (get-in selected ["runtime" "initializer"]) (get-in original ["runtime" "initializer"]))
               (or (= expected-role selected-role)
                   (and (= expected-role "value") (#{"closed" "ground"} selected-role))))
          "Selected canonical row conflicts with genuine startup observation")))
(defn- callable-abi [row]
  (let [f (get-in row ["ir" "fdecl"])] {"name" (get f "f") "xs" (get f "xs") "type" (get f "type")}))
(defn- validate-combined! [payload]
  (need (contains? #{"native-project-build-evidence/2" "lean-native-local-project/2"} (:profile payload)) "Build/artifact receipt profile differs")
  (let [index (:rows payload) entries (vector! (:entries payload) 16)
        _ (need (and (map? index) (<= 1 (count index) 4096) (seq entries)) "Bounded complete program required")
        rows (vec (vals index)) _ (bounded-rows! (into rows entries))
        plan (startup/validate-capture (:startup payload))
        labels (mapv #(name-label (get % "name")) rows)]
    (need (= (count labels) (count (set labels))) "Typed Name display collision in program")
    (doseq [[name row] index]
      (#'startup/name! name)
      (need (= name (get row "name")) "Canonical row key differs")
      (doseq [dependency (vector! (get row "dependencies") 8192)]
        (#'startup/name! dependency)
        (need (contains? index dependency) "Selected combined declaration closure incomplete")))
    (doseq [row (:rows plan)] (startup-observation! (get index (get row "name")) row))
    (doseq [entry entries]
      (need (and (#{"io-unit" "nat-to-nat" "string-to-string"} (get-in entry ["typeCheck" "signature"]))
                 (= "Lean.Meta.isDefEq" (get-in entry ["typeCheck" "algorithm"]))
                 (= "default" (get-in entry ["typeCheck" "transparency"]))
                 (empty? (get entry "levelParams"))) "Missing checked supported entry evidence")
      (doseq [role ["raw" "callable"]]
        (need (= (get entry role) (callable-abi (get index (get-in entry [role "name"])))) "Original entry callable differs")))
    {:plan plan :rows (vec (sort-by #(name-label (get % "name")) rows)) :entries entries}))
(defn- prepare-payload! [basis payload codec-bytes]
  (let [{:keys [plan rows entries]} (validate-combined! payload)
        _ (need (and (= (class (byte-array 0)) (class codec-bytes)) (<= (alength ^bytes codec-bytes) 16384)) "Bounded codec byte array required")
        codec (aclone ^bytes codec-bytes)]
    (need (= "53b224c8fa037b144260872e3b14878aff86dbb61b598e1ea49f991dabc1fb6b" (#'startup/sha codec)) "Independent codec layout witness differs")
    (#'startup/publish-prepared! basis plan rows
      {"native-project-manifest" (:manifest-sha256 payload) "profile" (:profile payload)
       "native-evidence-files" (or (:evidence-files payload) (:artifact-file-records payload))
       "entry-helper" (:entry-helper payload) "startup-helper" (get-in payload [:build-inputs "helper"])} codec entries)))
(defn prepare!
  "Research path overload over an actually issued native BuildReceipt."
  [basis actual-build-receipt codec-witness-path]
  (let [payload ((requiring-resolve 'ansatz.lean.jvm.compiler.evidence/authenticated-build) actual-build-receipt)]
    (prepare-payload! basis payload (#'startup/read-bytes! codec-witness-path 16384))))
(defn prepare-build-bytes!
  "Source publisher with SDK-owned codec resource bytes; never accepts a payload map."
  [basis actual-build-receipt codec-bytes]
  (prepare-payload! basis ((requiring-resolve 'ansatz.lean.jvm.compiler.evidence/authenticated-build) actual-build-receipt) codec-bytes))
(defn prepare-artifact!
  "Pure JVM publisher over an actual ArtifactReceipt and SDK-owned codec bytes.
   Resolving this accessor never discovers a toolchain or loads the build service."
  [basis actual-artifact-receipt codec-bytes]
  (prepare-payload! basis ((requiring-resolve 'ansatz.lean.jvm.artifact/authenticated-artifact) actual-artifact-receipt) codec-bytes))
