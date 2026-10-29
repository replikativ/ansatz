(ns java-ir-pure-provider
  "Opt-in research selector beneath resident admission. No frontend substitute."
  (:require [clojure.walk :as walk]
            [java-ir-pure-region :as region]
            [prototype.eval-const :as eval]
            [prototype.kernel-host :as kernel]
            [prototype.module-import :as imports]
            [prototype.raw-interop :as raw])
  (:import [ansatz.kernel Name Expr ConstantInfo Env]))

(defn kernel-name [name]
  (loop [name name parts []]
    (let [[kind parent value] name]
      (case kind
        "anonymous" (reduce (fn [^Name prefix [kind value]]
                              (case kind
                                "str" (Name/mkStr prefix value)
                                "num" (Name/mkNum prefix (Long/parseLong (str value)))))
                            Name/ANONYMOUS_NAME (rseq parts))
        ("str" "num") (recur parent (conj parts [kind value]))
        (throw (ex-info "Invalid structured Lean Name" {}))))))

(defn- atomic-type [^Expr type]
  (when (and type (= Expr/CONST (.-tag type))
             (empty? (seq (.-o1 type))))
    (let [name (.-o0 type)]
      (cond (= name (Name/mkStr Name/ANONYMOUS_NAME "Nat")) :nat
            (= name (Name/mkStr Name/ANONYMOUS_NAME "String")) :string))))

(defn logical-signature
  "Classify an already checked definition in a BORROWED Env. This function does
   not check or authenticate an Env. Exact explicit Nat/String types only; no
   aliases, universe parameters, proofs, dependent/implicit/instance arguments."
  [^Env env source-name]
  (when-let [^ConstantInfo info (.lookup env (kernel-name source-name))]
    (when (and (= ConstantInfo/DEF (.-tag info)) (zero? (.-safety info))
               (empty? (seq (.-levelParams info))))
      (loop [^Expr type (.-type info) arguments []]
        (if (= Expr/FORALL (.-tag type))
          (when-let [descriptor (atomic-type (.-o1 type))]
            (when (and (= :default (.-o3 type)) (< (count arguments) 64))
              (recur (.-o2 type) (conj arguments descriptor))))
          (when-let [result (atomic-type type)]
            {:arguments arguments :result result}))))))

(defn- original-rows [prepared target]
  (let [world (:world prepared) catalogue (:catalogue prepared)
        read-row (fn [name]
                   (or (get-in world [:eval-const-authorizations :declarations name])
                       (if-let [reader (:read-declaration catalogue)]
                         (reader name) (get-in catalogue [:declarations name]))))]
    (loop [pending [target] seen #{} rows []]
      (if (empty? pending) rows
        (let [name (peek pending) pending (pop pending)]
          (if (contains? seen name) (recur pending seen rows)
            (let [function (get-in world [:functions name]) row (read-row name)]
              (when-not (and function row (= name (:name row)))
                (throw (ex-info "Pure provider lacks original admitted row" {:name name})))
              (when (or (:raw-extern function) (:runtime-extern function)
                        (:redirect row) (get-in row [:ir :extern]))
                (throw (ex-info "First pure provider excludes externs and redirects" {:name name})))
              (recur (into pending (eval/executable-dependencies function))
                     (conj seen name) (conj rows (walk/stringify-keys row))))))))))

(defn- observe! [observer event]
  ;; Diagnostic callbacks have no authority over a completed guest invocation.
  (try (observer event) (catch Throwable _ nil)))

(defn selector
  "Create a trusted selector for resident/call-with-executor. The normal resident
   gate validates source/target/closure before selection. This selector resolves
   the CURRENT checked Env through protected guest helpers under that same lock,
   classifies the logical source root, and validates original rows against the
   selected legacy executable image. No raw code acquires checking authority.

   Unsupported profiles select ordinary execution before application entry.
   Once a Java plan starts, errors propagate with actual ownership evidence.
   OBSERVE receives best-effort bounded facts, never a World or Node. Observer
   failures are ignored and cannot turn a completed call into failed ownership."
  ([basis] (selector basis (fn [_])))
  ([basis observe]
   (fn [{:keys [prepared configuration target source-name abi signature]}]
     (let [progress (volatile! (:world prepared)) active (volatile! (:session prepared))
           invoke (fn [world target args]
                    (vreset! progress world)
                    (let [result (raw/call @active world target args)]
                      (vreset! progress (:state result)) (vreset! active (:session result))
                      [(:state result) (:value result)]))]
       (try
         (let [[world checked] (kernel/inherit-checked-association
                                {:invoke invoke} (:world prepared) (:environment prepared)
                                (or (:kernel-helpers configuration) imports/helpers))
               _ (vreset! progress world)
               prepared (assoc prepared :world world :session @active)
               logical (when checked (logical-signature checked source-name))
               attempt (when (= logical signature)
                         ;; Preparation can decline; it has neither encoded guest
                         ;; application arguments nor entered a Java engine.
                         (try {:plan (region/prepare basis (original-rows prepared target)
                                                     {:functions (:functions world) :target target
                                                      :params (mapv (fn [codec param]
                                                                      {:codec codec :borrow (:borrow param)})
                                                                    (:arguments logical) (:params abi))
                                                      :result (:result logical)})}
                              (catch clojure.lang.ExceptionInfo _ {:declined true})))
               plan (:plan attempt)]
           (observe! observe {:event :selection :tier (if plan :java-pure :ordinary) :target target})
           {:prepared prepared
            :invoke (if-not plan raw/call
                      (fn [session world invoked-target args]
                        (when-not (= target invoked-target)
                          (throw (ex-info "Pure provider target changed" {:checkpoint world})))
                        (try
                          (let [state (plan world args)]
                            (observe! observe {:event :completion :tier :java-pure :target target})
                            {:state state :session session :value (:result state)})
                          (catch Throwable cause
                            (throw (ex-info "Pure provider invocation failed"
                                            (assoc (ex-data cause) :checkpoint-session session) cause))))))})
         (catch Throwable cause
           (throw (ex-info "Pure provider selection failed"
                           (merge {:checkpoint @progress :checkpoint-session @active} (ex-data cause)) cause))))))))
