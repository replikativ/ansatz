(ns prototype.cases-on-preparation
  "Host-only, explicit replacement of one authenticated deferred extern before
   executable profile sealing. Construction remains guest code; admission stays
   with the existing kernel. No execution, initialization, or guest allocation."
  (:require [clojure.data.json :as json]
            [prototype.checkpoint-wire :as wire]
            [prototype.declaration-store :as declarations]
            [prototype.source-inductive-preparation :as source]
            [prototype.preparation :as preparation]
            [prototype.runtime-abi :as abi]
            [prototype.raw-interop :as raw]
            [prototype.eval-const :as eval]))

(def helper ["str" ["str" ["anonymous"] "KernelCasesOnRaw"] "construct"])
(def signature {:params [{:ty "object" :borrow false} {:ty "tobject" :borrow true}]
                :return-type "object"})
(def original-row-sha256 "d7a54765268331ebe9afdfa4695a7702b8d53c95cd1a8c51da8ef41d1468e43d")
(def ^:private native-symbol "lean_mk_cases_on")
(defn- check! [ok message] (when-not ok (throw (ex-info message {}))))
(defn- row [catalogue name]
  (if-let [read! (:read-declaration catalogue)] (read! name)
      (get-in catalogue [:declarations name])))
(defn- shape [f]
  {:params (mapv #(select-keys % [:ty :borrow]) (:xs f)) :return-type (:type f)})
(defn- options [session]
  ;; A replacement must not retain compiled blocks from the old program.
  (select-keys session [:backend :fuel :compile-threshold]))

(defn prepare
  "Return a NEW coherent {:candidate :configuration :profile}. ARTIFACT is the
   authenticated helper source/IR packet accepted by authenticated-index.
   CONFIGURATION additionally retains :cases-on-original-row-bytes and explicit
   :cases-on-original-function (nil means absent from the original independent
   registry). These are trusted host inputs, never recovered from CANDIDATE.
   Existing original CAS bytes, trap shape, ABI and all other executable/binding
   identities are checked. Only the named trap may change. No owners acquired."
  [candidate configuration artifact]
  (try
    (let [world (:world candidate) session (:session candidate)
          support (:support candidate) trusted (:trusted-functions configuration)
          bindings (:trusted-bindings configuration) catalogue (:catalogue configuration)
          _ (doseq [packet [candidate configuration]
                    key [:graph-profile :graph-install-options :prefix :context]]
              (check! (not (contains? packet key)) "casesOn replacement must precede profile/prefix sealing"))
          _ (doseq [packet [candidate configuration]]
              (check! (nil? (get-in packet [:frontend-configuration :install-options]))
                      "casesOn cannot replace a sealed evaluator profile"))
          _ (check! (and (= :done (:status world)) (empty? (:frames world))
                         (nil? (:host-request world)) (map? trusted) (seq trusted)
                         (map? bindings) (map? support)
                         (empty? (get-in world [:eval-const-authorizations :units]))
                         (identical? (:functions world) (:functions session))
                         (identical? catalogue (:catalogue candidate))
                         (identical? trusted (:trusted-functions candidate))
                         (identical? trusted (get-in support [:session :functions]))
                         (identical? bindings (get-in support [:session :bindings]))
                         (= (set (keys bindings)) (set (keys (:bindings session)))))
                    "casesOn requires coherent independent pre-user preparation")
          _ (doseq [[symbol binding] bindings]
              (check! (identical? binding (get-in session [:bindings symbol]))
                      "casesOn original binding identity drift"))
          _ (check! (not (contains? bindings native-symbol))
                    "casesOn symbol already bound; explicit guest redirect required")
          bytes (:cases-on-original-row-bytes configuration)
          _ (check! (and (bytes? bytes) (<= (alength ^bytes bytes) 65536)
                         (= original-row-sha256 (wire/sha256 bytes)))
                    "casesOn original CAS bytes mismatch")
          original (json/read-str (wire/utf8-string bytes) :key-fn keyword)
          ext (get-in original [:ir :extern]) target (:name original)
          _ (check! (and (= "decl" (:kind original)) (= target (:f ext))
                         (= native-symbol (abi/symbol-for ext))
                         (= signature (shape ext)) (nil? (:redirect original))
                         (wire/same-data? original (row catalogue target)))
                    "casesOn original catalogue row/name/ABI mismatch")
          expected-old (second (abi/lower-deferred original))
          actual-old (get-in world [:functions target]) old (get trusted target)
          _ (check! (and (contains? configuration :cases-on-original-function)
                         actual-old (wire/same-data? expected-old actual-old)
                         (= native-symbol (get-in expected-old [:deferred-extern :symbol]))
                         (if-let [independent (:cases-on-original-function configuration)]
                           (and (identical? independent old) (identical? independent actual-old))
                           (nil? old)))
                    "casesOn original executable is not the independently retained trap")
          _ (doseq [[name function] trusted :when (not= name target)]
              (check! (identical? function (get-in world [:functions name]))
                      "casesOn unrelated executable identity drift"))
          authorized (get-in world [:eval-const-authorizations :functions target])
          _ (when authorized
              (check! (identical? authorized actual-old) "casesOn imported authority identity drift"))
          index (source/authenticated-index artifact)
          _ (check! (not (contains? (:declarations index) target))
                    "casesOn helper must not overwrite the original producer row")
          overlaid (declarations/overlay catalogue index)
          _ (doseq [name (keys (:declarations index))] (row overlaid name))
          helper-row (row overlaid helper) f (get-in helper-row [:ir :fdecl])
          _ (check! (and f (= helper (:name helper-row) (:f f)) (= signature (shape f)))
                    "casesOn helper body/ownership ABI mismatch")
          ;; Keep producer rows/CAS unchanged. The explicit consumer capability
          ;; also applies when future imports pass an original unmodified row.
          consumer (abi/with-consumer-redirects overlaid
                     {native-symbol {:original-row original :target helper}})
          lower (fn [r]
                  (if (contains? bindings (some-> r :ir :extern abi/symbol-for))
                    (raw/lower bindings r) (abi/lower-deferred-catalogue consumer r)))
          replacement (second (abi/lower-catalogue consumer original))
          derived (preparation/complete-functions consumer (assoc trusted target replacement)
                                                  [target] lower)
          functions (reduce-kv
                     (fn [out name function]
                       (when-let [existing (get out name)]
                         (check! (or (= target name) (identical? existing function))
                                 "casesOn helper closure collides with existing executable"))
                       (assoc out name function)) (:functions world) derived)
          next-world (cond-> (assoc world :functions functions)
                       authorized (assoc-in [:eval-const-authorizations :functions target] replacement))
          closure (eval/validate-executables! next-world derived [target])
          _ (doseq [[name function] closure]
              (check! (not (or (:deferred-extern function) (:deferred-declaration function)))
                      "casesOn helper closure has an unresolved runtime frontier")
              (when (:runtime-initializer function)
                (check! (= :ready (get-in world [:globals name :status]))
                        "casesOn helper needs an uninitialized imported global")))
          next-support (assoc support :catalogue consumer
                              :session (raw/open-functions derived bindings (options (:session support))))
          inherited-lower (:consumer-extern-lower configuration)
          _ (check! (or (nil? inherited-lower) (fn? inherited-lower))
                    "casesOn inherited consumer lowerer is malformed")
          lower-extern (fn [r]
                         (if (= native-symbol (some-> r :ir :extern abi/symbol-for))
                           (abi/lower-catalogue consumer r)
                           (when inherited-lower (inherited-lower r))))
          next-candidate (assoc candidate :world next-world :catalogue consumer
                                :trusted-functions derived :support next-support
                                :session (raw/open-functions functions bindings (options session)))
          next-configuration (assoc configuration :catalogue consumer :trusted-functions derived
                                   :consumer-extern-lower lower-extern)]
      {:candidate next-candidate :configuration next-configuration
       ;; The enclosing profile composes this with its existing custom extern
       ;; lowerer when it finally creates frontend/evaluator install-options.
       ;; Returning a narrow callback avoids prematurely sealing that profile.
       :lower-extern lower-extern
       :profile {:id "ansatz-raw-cases-on/1" :stage :before-profile-sealing
                 :original-row-sha256 original-row-sha256
                 :helper-source-sha256 (:source-sha256 artifact) :helper-ir-sha256 (:ir-sha256 artifact)
                 :relinked [target] :target helper :signature signature
                 :guest-executed false :new-initialization-actions 0
                 :imported-function-authority-updated? (boolean authorized)}})
    (catch Throwable cause
      (throw (ex-info "Raw casesOn pre-seal preparation failed"
                      {:cases-on-preparation-entry candidate
                       :cases-on-preparation-configuration configuration} cause)))))
