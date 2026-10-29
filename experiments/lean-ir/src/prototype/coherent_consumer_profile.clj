(ns prototype.coherent-consumer-profile
  "One closed current-cohort consumer of the unchanged producer50f archive.
   Reviewed contract bytes pin members/composition; a fresh trusted launcher
   separately attests namespace selection and prohibits reload/redefs. No guest
   execution, kernel admission, readiness, or callback authority is issued here."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [prototype.checkpoint-wire :as wire]
            [prototype.globals-consumer-profile :as old])
  (:import [java.io PushbackReader StringReader]
           [java.nio.charset StandardCharsets]
           [java.nio.file Files]
           [java.security MessageDigest]))

(def profile-id old/coherent-frontend-profile-id)
(def cases-on-target ["str" ["str" ["anonymous"] "KernelCasesOnRaw"] "construct"])
(def schema "ansatz-coherent-frontend-contract/1")
(def jvm-profile-id old/coherent-jvm-application-profile-id)
(def jvm-schema "ansatz-coherent-jvm-application-contract/1")
(def jvm-stages
  [:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio :cases-on :seal :helper-value
   :init-prefix :load-a :select-a :call-a :callback :load-b :select-b :call-b-a :dispose])
(def lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def target {:triple "x86_64-unknown-linux-gnu" :word-bits 64})
;; EXACT original producer PRECHECK policy. This is not the effective post-user
;; kernel binding policy; ordinary/nested restrictions and checker fuel there
;; remain governed by their existing preparation APIs without any widening.
(def kernel-policy {:allow-axioms? true :allow-unsafe? true :allow-compiler-markers? true})
(def cases-on-original-row-sha256 "d7a54765268331ebe9afdfa4695a7702b8d53c95cd1a8c51da8ef41d1468e43d")
(def max-contract-bytes (* 4 1024 1024))
(def artifact-base-profile-id :full-init-lean-4.33.1-producer50f)
(def option-keys
  (conj old/option-keys :consumer-contract-source :expected-consumer-contract-sha256))
(def ^:private required-inputs
  {"prototype/coherent_consumer_profile.clj" :host-source
   "prototype/globals_consumer_profile.clj" :host-source
   "prototype/globals_consumer_factory.clj" :host-source
   "prototype/restore_consumer.clj" :host-source
   "ansatz/kernel/TypeChecker.class" :kernel-class
   "ansatz/kernel/Env.class" :kernel-class
   "ansatz/kernel/Expr.class" :kernel-class})
(def ^:private stage-order
  [:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio :cases-on
   :seal :helper-value :project :typed-io :ordinary-module :chain :diamond :reload])
(def ^:private stage-rank (zipmap stage-order (range)))

(defn- exact! [value expected label]
  (wire/check (and (map? value) (= expected (set (keys value)))) (str "Invalid coherent " label)))
(defn- bounded-vector! [v limit label]
  (wire/check (and (vector? v) (<= (count v) limit)) (str "Invalid coherent " label)))
(defn- id! [id]
  (wire/check (and (string? id) (<= 1 (count id) 512)
                   (re-matches #"[A-Za-z0-9_./$-]+" id)
                   (not (str/starts-with? id "/"))
                   (not-any? #{"" "." ".."} (str/split id #"/" -1)))
              "Invalid coherent relative input ID"))
(defn- name! [value]
  ;; Typed Lean Name JSON shape, bounded without relying on a dotted spelling.
  (loop [value value left 128]
    (wire/check (and (pos? left) (vector? value)) "Invalid coherent Lean Name")
    (case (first value)
      "anonymous" (wire/check (= ["anonymous"] value) "Invalid coherent anonymous Name")
      "str" (do (wire/check (and (= 3 (count value)) (string? (nth value 2))
                                  (<= (count (nth value 2)) 512)) "Invalid coherent string Name")
                (recur (second value) (dec left)))
      "num" (do (wire/check (and (= 3 (count value)) (integer? (nth value 2))
                                  (<= 0 (nth value 2) Long/MAX_VALUE)) "Invalid coherent numeric Name")
                (recur (second value) (dec left)))
      (wire/fail "Invalid coherent Name constructor" {}))))
(defn- entries! [values]
  (bounded-vector! values 64 "entrypoints")
  (wire/check (and (seq values) (= (count values) (count (set values)))) "Duplicate/empty coherent entrypoints")
  (doseq [entry values]
    (wire/check (and (string? entry) (<= 1 (count entry) 512)
                     (re-matches #"[A-Za-z0-9_.!?*/$<>-]+" entry)) "Invalid coherent entrypoint")))
(defn- class-source [id]
  (let [outer (first (str/split (subs id 0 (- (count id) 6)) #"\$"))]
    (if (= outer "prototype/TypedLongMemo") "java/prototype/TypedLongMemo.java"
        (str "src-java/" outer ".java"))))

(def execution-roles
  {:frontend {:backend :mutable :fuel 500000000 :compile-threshold 1}
   :application {:backend :jvm :fuel 500000000 :compile-threshold 1}})
(def selection-limits
  {:max-functions 16 :max-descriptors 64 :max-work 100000 :max-source-bytes 16384})
(def ^:private application-codecs #{:uint8 :uint16 :uint32 :uint64 :usize :nat})
(defn- scalar-value! [value]
  (wire/check (and (integer? value) (<= 0 value 18446744073709551615N)) "Bounded immutable numeric application value required"))
(defn- call-signature! [signature]
  (exact! signature #{:arguments :result} "application call signature")
  (bounded-vector! (:arguments signature) 4 "application arguments")
  (wire/check (and (every? application-codecs (:arguments signature)) (application-codecs (:result signature)))
              "Unsupported finite application codec"))
(defn validate-application!
  "Closed inert policy for this finite slice; confers no code/binding authority."
  [application]
  (exact! application #{:execution-roles :transition :corpus :callback :selection-limits} "application policy")
  (wire/check (and (= execution-roles (:execution-roles application)) (= [:mutable :jvm] (:transition application))
                   (= selection-limits (:selection-limits application))) "Unapproved finite execution/selection policy")
  (bounded-vector! (:corpus application) 4 "application corpus")
  (wire/check (and (seq (:corpus application))
                   (= (count (:corpus application)) (count (set (map :id (:corpus application)))))) "Duplicate/empty corpus")
  (let [sources (mapcat (juxt :source-a-id :source-b-id) (:corpus application))]
    (wire/check (= (count sources) (count (set sources))) "Corpus requires distinct A/B capture input IDs"))
  (doseq [row (:corpus application)]
    (exact! row #{:id :module :source-a-id :source-b-id :entry :worker :signature :calls :fallback} "corpus row")
    (doseq [key [:id :source-a-id :source-b-id]] (id! (get row key)))
    (wire/check (not= (:source-a-id row) (:source-b-id row)) "A/B captures must be distinct inputs")
    (doseq [key [:module :entry :worker]] (name! (get row key)))
    (call-signature! (:signature row))
    (bounded-vector! (:calls row) 4 "application calls")
    (wire/check (seq (:calls row)) "At least one actual application call required")
    (doseq [call (:calls row)]
      (exact! call #{:args :expected-a :expected-b} "application call")
      (bounded-vector! (:args call) 4 "application argument values")
      (wire/check (= (count (:args call)) (count (get-in row [:signature :arguments]))) "Application argument arity mismatch")
      (doseq [v (concat (:args call) [(:expected-a call) (:expected-b call)])] (scalar-value! v)))
    (let [fallback (:fallback row)]
      (exact! fallback #{:entry :signature :args :expected} "fallback control")
      (name! (:entry fallback)) (call-signature! (:signature fallback))
      (bounded-vector! (:args fallback) 4 "fallback values")
      (wire/check (= (count (:args fallback)) (count (get-in fallback [:signature :arguments]))) "Fallback arity mismatch")
      (doseq [v (conj (:args fallback) (:expected fallback))] (scalar-value! v))))
  (let [callback (:callback application)]
    (exact! callback #{:symbol :entry :signature :arguments :result :input :expected :implementation} "callback")
    (wire/check (and (string? (:symbol callback)) (re-matches #"[A-Za-z_][A-Za-z0-9_]{0,255}" (:symbol callback))
                     (= :utf8-length (:implementation callback)) (= :nat (:result callback))
                     (string? (:input callback)) (<= (count (:input callback)) 4096)
                     (= (count (.getBytes ^String (:input callback) StandardCharsets/UTF_8)) (:expected callback)))
                "Only the fixed bounded String-to-Nat callback is supported")
    (name! (:entry callback))
    (exact! (:signature callback) #{:params :return-type} "callback ABI")
    (bounded-vector! (get-in callback [:signature :params]) 1 "callback ABI parameters")
    (bounded-vector! (:arguments callback) 1 "callback argument codecs")
    (wire/check (= 1 (count (get-in callback [:signature :params])) (count (:arguments callback))) "One callback argument required")
    (let [param (first (get-in callback [:signature :params])) argument (first (:arguments callback))]
      (exact! param #{:ty :borrow} "callback ABI parameter")
      (exact! argument #{:codec :ownership} "callback codec")
      (wire/check (and (#{"object" "tobject" "tagged"} (:ty param)) (boolean? (:borrow param))
                       (#{"object" "tobject" "tagged"} (get-in callback [:signature :return-type]))
                       (= :string (:codec argument)) (= (if (:borrow param) :borrowed :owned) (:ownership argument)))
                  "Callback codec/ownership differs from declared ABI")))
  application)

(defn- validate-contract*
  "Validate closed build data against an independently accepted implementation
   identity. Callers must authenticate exact contract bytes BEFORE parsing them.
   Returns the same contract; does not resolve files or authorize guest code."
  [contract expected-implementation selected-profile selected-schema selected-stage-rank]
  (exact! contract (cond-> #{:schema :profile :producer :lean-commit :target :inventory
                             :implementation-sha256 :composition :kernel-policy :limits}
                    (contains? contract :kernel-base-admission) (conj :kernel-base-admission)) "contract")
  (when (contains? contract :kernel-base-admission)
    (wire/check (= jvm-profile-id selected-profile)
                "Artifact base admission requires the finite JVM provider profile")
    (wire/check (= {:basis :trusted-artifact :profile artifact-base-profile-id}
                   (:kernel-base-admission contract))
                "Unsupported explicit kernel base admission profile"))
  (exact! (:producer contract) #{:implementation-sha256 :recipe-sha256} "producer identity")
  (exact! (:limits contract) #{:max-helper-bytes :max-helper-declarations :checker-fuel} "limits")
  (wire/check (and (= selected-schema (:schema contract)) (= selected-profile (:profile contract))
                   (= {:implementation-sha256 old/producer-implementation-sha256
                       :recipe-sha256 old/producer-recipe-sha256} (:producer contract))
                   (= lean-commit (:lean-commit contract)) (= target (:target contract))
                   (= kernel-policy (:kernel-policy contract))) "Coherent fixed contract identity/policy mismatch")
  (doseq [[key bound] {:max-helper-bytes wire/max-row-bytes
                       :max-helper-declarations 1000000 :checker-fuel Long/MAX_VALUE}]
    (wire/check (and (integer? (get-in contract [:limits key]))
                     (<= 1 (get-in contract [:limits key]) bound)) "Invalid coherent finite limit"))
  (let [inventory (:inventory contract)
        implementation (old/consumer-identity inventory)
        by-id (into {} (map (juxt :id identity)) inventory)
        composition (:composition contract)]
    (wire/check (and (wire/hash? expected-implementation)
                     (= expected-implementation (:implementation-sha256 contract) implementation))
                "Coherent implementation digest mismatch")
    (doseq [{:keys [id kind]} inventory]
      (id! id)
      (wire/check (not (contains? old/excluded-producer-sources id)) "Coherent selected producer-only source")
      (when (contains? #{:kernel-class :runtime-class} kind)
        (wire/check (and (str/ends-with? id ".class")
                         (= (= :kernel-class kind) (str/starts-with? id "ansatz/kernel/"))
                         (not (str/ends-with? id "__init.class"))
                         (= :host-source (get-in by-id [(class-source id) :kind])))
                    "Coherent class missing source provenance/AOT prohibited")))
    (doseq [[id kind] required-inputs]
      (wire/check (= kind (get-in by-id [id :kind])) "Coherent essential member missing/role mismatch"))
    (exact! composition (cond-> #{:controllers :helpers :redirects :stages}
                           (= jvm-profile-id selected-profile) (conj :application)) "composition")
    (when (= jvm-profile-id selected-profile) (validate-application! (:application composition)))
    (doseq [[key maximum] {:controllers 64 :helpers 32 :redirects 16 :stages 32}]
      (bounded-vector! (get composition key) maximum (name key)))
    (wire/check (and (seq (:controllers composition))
                     (= (count (:controllers composition)) (count (set (map :id (:controllers composition))))))
                "Duplicate/empty coherent controllers")
    (doseq [controller (:controllers composition)]
      (exact! controller #{:id :entrypoints} "controller")
      (id! (:id controller))
      (wire/check (= :host-source (get-in by-id [(:id controller) :kind])) "Coherent controller not selected source")
      (entries! (:entrypoints controller)))
    (wire/check (seq (:helpers composition)) "Coherent helper inventory is empty")
    (wire/check (= (count (:helpers composition)) (count (set (map :id (:helpers composition)))))
                "Duplicate coherent helper")
    (doseq [helper (:helpers composition)]
      (exact! helper #{:id :source-id :source-sha256 :ir-id :ir-sha256 :entrypoints} "helper")
      (doseq [key [:id :source-id :ir-id]] (id! (get helper key)))
      (doseq [key [:source-sha256 :ir-sha256]]
        (wire/check (wire/hash? (get helper key)) "Invalid coherent helper digest"))
      (entries! (:entrypoints helper)))
    (let [cases-on (filter #(= "cases-on" (:id %)) (:helpers composition))]
      (wire/check (and (= 1 (count cases-on))
                       (= ["KernelCasesOnRaw.construct"] (:entrypoints (first cases-on))))
                  "Coherent exact casesOn helper identity required"))
    (wire/check (= 1 (count (:redirects composition))) "Coherent casesOn redirect required")
    (wire/check (= (count (:redirects composition)) (count (set (map :symbol (:redirects composition)))))
                "Duplicate coherent construction redirect")
    (doseq [redirect (:redirects composition)]
      (exact! redirect #{:symbol :target :row-sha256} "construction redirect")
      (wire/check (and (= "lean_mk_cases_on" (:symbol redirect)) (= cases-on-original-row-sha256 (:row-sha256 redirect)))
                  "Unapproved coherent construction redirect")
      (name! (:target redirect))
      (wire/check (= cases-on-target (:target redirect)) "Coherent exact casesOn target mismatch"))
    (let [stages (:stages composition) positions (zipmap stages (range))]
      (wire/check (and (seq stages) (= (count stages) (count (set stages)))
                       (every? selected-stage-rank stages)
                       (apply < (map selected-stage-rank stages)) (= :fresh-init (first stages))
                       (integer? (:cases-on positions)) (integer? (:seal positions))
                       (< (:cases-on positions) (:seal positions))) "Invalid coherent stage order")))
  (when (= jvm-profile-id selected-profile)
    (wire/check (= jvm-stages (get-in contract [:composition :stages])) "Exact finite JVM application stages required"))
  contract)

(defn validate-contract! [contract expected-implementation]
  (validate-contract* contract expected-implementation profile-id schema stage-rank))
(defn validate-jvm-contract! [contract expected-implementation]
  (validate-contract* contract expected-implementation jvm-profile-id jvm-schema (zipmap jvm-stages (range))))

(defn- bounded-edn! [source]
  ;; Bound reader recursion before constructing data. Contracts use only maps,
  ;; vectors and scalar EDN, never lists, metadata, dispatch/tagged values or chars.
  ;; Strings/comments are scanned lexically so their delimiters have no effect.
  (loop [i 0 depth 0 quoted? false escaped? false comment? false forms 0]
    (if (= i (count source))
      (wire/check (and (zero? depth) (not quoted?)) "Invalid coherent contract delimiters")
      (let [c (.charAt ^String source i)]
        (cond
          comment? (recur (inc i) depth false false (not (contains? #{\newline \return} c)) forms)
          quoted? (recur (inc i) depth (or escaped? (not= c \"))
                         (and (not escaped?) (= c \\)) false forms)
          (= c \;) (recur (inc i) depth false false true forms)
          (= c \") (recur (inc i) depth true false false forms)
          (contains? #{\# \^ \\ \( \)} c) (wire/fail "Unsupported coherent contract reader syntax" {})
          (contains? #{\{ \[} c)
          (do (wire/check (and (< depth 256) (< forms 20000)) "Coherent contract depth/form limit")
              (recur (inc i) (inc depth) false false false (inc forms)))
          (contains? #{\} \]} c)
          (do (wire/check (pos? depth) "Invalid coherent closing delimiter")
              (recur (inc i) (dec depth) false false false forms))
          :else (recur (inc i) depth false false false forms)))))
  (with-open [reader (PushbackReader. (StringReader. source))]
    (let [eof (Object.)
          options {:eof eof :readers {} :default (fn [tag _] (wire/fail "Unsupported coherent contract tag" {:tag tag}))}
          value (edn/read options reader)]
      (wire/check (and (not (identical? eof value)) (identical? eof (edn/read options reader)))
                  "Coherent contract requires exactly one EDN value")
      value)))

(defn read-contract!
  "Digest exact bounded UTF-8 contract bytes before parsing/resolving anything.
   SOURCE is captured text, never a path; EXPECTED comes from trusted launcher."
  [source expected]
  (wire/check (and (string? source) (<= (count source) max-contract-bytes) (wire/hash? expected))
              "Explicit bounded coherent contract text/external digest required")
  (let [bytes (.getBytes ^String source StandardCharsets/UTF_8)]
    (wire/check (and (<= (alength bytes) max-contract-bytes) (= expected (wire/sha256 bytes)))
                "Coherent external contract digest mismatch")
    (bounded-edn! source)))

(defn- canonical-file [value] (.getCanonicalFile (io/file value)))
(defn- digest-stream [input]
  (let [digest (MessageDigest/getInstance "SHA-256") bytes (byte-array 65536)]
    (loop [] (let [n (.read ^java.io.InputStream input bytes)]
               (when (pos? n) (.update digest bytes 0 n) (recur))))
    (.formatHex (java.util.HexFormat/of) (.digest digest))))
(defn- selected-url! [loader id expected]
  (let [urls (vec (enumeration-seq (.getResources ^ClassLoader loader id)))]
    (wire/check (and (= 1 (count urls)) (= "file" (.getProtocol ^java.net.URL (first urls)))
                     (= expected (canonical-file (.toURI ^java.net.URL (first urls)))))
                "Coherent resource selection/duplicate/root mismatch")
    (first urls)))
(defn- aot-resource-id [id]
  (when-let [extension (cond (str/ends-with? id ".clj") 4 (str/ends-with? id ".cljc") 5)]
    (str (subs id 0 (- (count id) extension)) "__init.class")))
(defn- authenticate-selected! [row resolve-source]
  (let [{:keys [id kind sha256]} row
        file (canonical-file (resolve-source id))
        _ (wire/check (= sha256 (wire/file-sha256 file)) "Coherent selected input bytes drift")]
    (case (old/input-role row)
      (:java-source :provenance-source) nil
      :selected-resource
      (do (selected-url! (clojure.lang.RT/baseLoader) id file)
          (when-let [aot-id (aot-resource-id id)]
            (wire/check (nil? (io/resource aot-id)) "Coherent project AOT shadow")))
      :selected-class
      (let [class-name (subs (str/replace id "/" ".") 0 (- (count id) 6))
            loader (if (= :kernel-class kind) (.getClassLoader ansatz.kernel.TypeChecker)
                       (clojure.lang.RT/baseLoader))
            ;; Authenticate resource selection and file bytes before defining
            ;; the class where possible; false never runs static initialization.
            _ (selected-url! loader id file)
            class (Class/forName class-name false loader)
            actual-loader (.getClassLoader ^Class class)
            url (selected-url! actual-loader id file)
            code-url (some-> class .getProtectionDomain .getCodeSource .getLocation)]
        (wire/check (and code-url (= "file" (.getProtocol ^java.net.URL code-url)))
                    "Coherent class CodeSource unavailable/non-directory")
        (let [root (canonical-file (.toURI ^java.net.URL code-url))]
          (wire/check (and (.isDirectory root) (= file (canonical-file (io/file root id))))
                      "Coherent loaded class CodeSource mismatch"))
        (with-open [input (.getResourceAsStream ^Class class (str "/" id))]
          (wire/check (and input (= sha256 (digest-stream input))) "Coherent actual loaded class bytes drift"))
        ;; Return selected class root for an exact output inventory audit below.
        (canonical-file (.toURI ^java.net.URL code-url))))))

(defn- authenticate*
  "Host-only two-cohort authentication. Original producer bytes remain resolver-
   only provenance. Consumer disk selection, actual classes and fresh launcher
   attestation must all agree. Result retains the old exact descriptor shape."
  [{:keys [producer-preparation producer-recipe-source producer-resolve-artifact store-root
           consumer-inventory expected-consumer-implementation-sha256
           loaded-consumer-implementation-sha256 consumer-resolve-source
           consumer-contract-source expected-consumer-contract-sha256] :as options} validate selected-profile]
  (exact! options option-keys "factory options")
  ;; No resolver, selected namespace/class lookup, or producer parsing before pin.
  (let [contract (read-contract! consumer-contract-source expected-consumer-contract-sha256)]
    (validate contract expected-consumer-implementation-sha256)
    (wire/check (and (fn? producer-resolve-artifact) (fn? consumer-resolve-source)
                     (string? store-root) (seq store-root)
                     (= expected-consumer-implementation-sha256 loaded-consumer-implementation-sha256)
                     (wire/same-data? consumer-inventory (:inventory contract)))
                "Coherent explicit resolvers/loaded attestation/inventory mismatch")
    (old/producer-recipe! producer-preparation producer-recipe-source)
    (wire/check (= kernel-policy (:kernel-policy producer-preparation)) "Coherent producer kernel policy drift")
    (doseq [id old/excluded-producer-sources]
      (wire/check (and (nil? (io/resource id))
                       (nil? (io/resource (str (subs id 0 (- (count id) 4)) "__init.class"))))
                  "Coherent producer-only source/AOT selected"))
    (let [roots (set (keep #(authenticate-selected! % consumer-resolve-source) consumer-inventory))
          expected-classes (set (for [{:keys [id kind]} consumer-inventory
                                     :when (contains? #{:kernel-class :runtime-class} kind)] id))
          actual-classes
          (reduce (fn [out root]
                    (with-open [paths (Files/walk (.toPath ^java.io.File root) (make-array java.nio.file.FileVisitOption 0))]
                      (let [selected (vec (iterator-seq (.iterator (.limit paths 10001))))]
                        (wire/check (<= (count selected) 10000) "Coherent class directory traversal limit")
                        (reduce (fn [out path]
                                (let [file (.toFile ^java.nio.file.Path path)]
                                  (if (and (.isFile file) (str/ends-with? (.getName file) ".class"))
                                    (conj out (str (.relativize (.toPath ^java.io.File root) path))) out)))
                              out selected)))) #{} roots)]
      (wire/check (= expected-classes actual-classes) "Coherent extra/missing compiled class output"))
    (doseq [{:keys [source-id source-sha256 ir-id ir-sha256]} (get-in contract [:composition :helpers])
            [id expected] [[source-id source-sha256] [ir-id ir-sha256]]]
      (let [file (consumer-resolve-source id)
            bytes (wire/read-file-bytes file (get-in contract [:limits :max-helper-bytes]))]
        (wire/check (= expected (wire/sha256 bytes)) "Coherent helper source/IR drift")))
    {:description {:producer-preparation producer-preparation
                   :consumer-implementation-sha256 expected-consumer-implementation-sha256
                   :compatibility-profile selected-profile
                   :consumer-contract-sha256 expected-consumer-contract-sha256}
     :consumer-contract-sha256 expected-consumer-contract-sha256
     :contract contract}))

(defn authenticate! [options]
  (authenticate* options validate-contract! profile-id))
(defn authenticate-jvm! [options]
  (authenticate* options validate-jvm-contract! jvm-profile-id))
