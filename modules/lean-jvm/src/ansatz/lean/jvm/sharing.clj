(ns ansatz.lean.jvm.sharing
  "Conservative pre-admission proof for sharing diagnostics on managed values.
   Authenticated startup rows/entries are inputs, never caller certificates."
  (:require [ansatz.lean.jvm.entry :as entry]
            [ansatz.lean.jvm.signature :as signature]))

(def ^:private factories
  #{"ARRAY_MK" "ARRAY_EMPTY" "ARRAY_PUSH" "ARRAY_POP" "ARRAY_REPLICATE"
    "ARRAY_FSET" "ARRAY_USET" "ARRAY_SWAP" "BYTE_MK" "BYTE_EMPTY" "BYTE_PUSH"})
(def ^:private managed-host-kinds
  #{"array" "bytes" "list" "product" "option" "sum" "except" "bool" "unit"})
(def ^:private maximum-work 200000)
(defn- refuse! [reason]
  (throw (ex-info (str "Sharing diagnostic value domain is not established: " reason)
                  {:code "CapabilityMissing" :restriction :sharing-managed-domain})))
(defn- need! [condition reason] (when-not condition (refuse! reason)))
(defn- parameter-key [f i] [f :parameter i])
(defn- variable-key [f i] [f :variable i])
(defn- return-key [f] [f :return])
(def ^:private immediate ::immediate)
(defn- argument-key [environment argument]
  (if (= "erased" argument) immediate
    (or (get environment (get-in argument ["var" "id" "idx"]))
        (refuse! "unbound value argument"))))

(defn check!
  "Check the complete selected closure before engine construction. Only active
   for actual DBG_TRACE_SHARED requirements. Unknown provenance fails closed;
   Java String/BigInteger are not silently classified as persistent atoms."
  [rows entries requirements]
  (let [externs (:externs requirements)
        debug (set (for [[n requirement] externs
                         :when (= "DBG_TRACE_SHARED" (:field requirement))] n))]
    (when (seq debug)
      (let [work (volatile! 0)
            tick! (fn []
                    (vswap! work inc)
                    (when (> @work maximum-work) (refuse! "analysis work budget"))
                    (when (.isInterrupted (Thread/currentThread))
                      (throw (ex-info "Sharing analysis interrupted" {:code "Cancelled"}))))
            by-name (into {} (map (juxt #(get % "name") identity) rows))
            declarations (into {} (for [[n row] by-name :let [d (get-in row ["ir" "fdecl"])] :when d] [n d]))
            recipes (atom {immediate {:anchor true}})
            seeds (atom []) paps (atom #{}) required-parameters (atom #{})
            define! (fn [key recipe]
                      (tick!) (need! (not (contains? @recipes key)) "duplicate IR binder")
                      (swap! recipes assoc key recipe))
            append! (fn [key dependency]
                      (tick!) (swap! recipes update-in [key :dependencies] (fnil conj []) dependency))]
        (need! (= (count rows) (count by-name)) "duplicate declaration")
        (doseq [[f d] declarations]
          (define! (return-key f) {:dependencies []})
          (doseq [[i _] (map-indexed vector (get d "xs"))]
            (define! (parameter-key f i) {:dependencies [] :parameter f})))
        (letfn [(expression! [environment expression]
                  (tick!) (need! (= 1 (count expression)) "malformed expression")
                  (let [[op data] (first expression)]
                    (case op
                      "ctor" {:anchor true}
                      "pap" (do (swap! paps conj (get data "c")) {:anchor true})
                      "lit" (let [n (get-in data ["v" "num" "v"])]
                              (if (and (integer? n) (<= 0 n Long/MAX_VALUE))
                                {:anchor true} {:unsupported "heap leaf literal"}))
                      "fap"
                      (let [target (get data "c") arguments (get data "ys")
                            keys (mapv #(argument-key environment %) arguments)
                            declaration (get declarations target)
                            field (get-in externs [target :field])]
                        (when declaration
                          (need! (= (count keys) (count (get declaration "xs"))) "direct call arity")
                          (doseq [[i key] (map-indexed vector keys)]
                            (append! (parameter-key target i) key)))
                        (cond
                          (contains? debug target)
                          (do (need! (= 3 (count keys)) "diagnostic arity")
                              (swap! seeds conj (nth keys 2))
                              {:dependencies [(nth keys 2)]})
                          (contains? factories field) {:anchor true}
                          declaration {:dependencies [(return-key target)]}
                          :else {:unsupported "external return"}))
                      ;; A projection may select an untracked heap leaf; an
                      ;; object lane or managed parent does not prove otherwise.
                      {:unsupported (str "expression " op)})))
                (body! [f environment joins body depth]
                  (tick!) (need! (< depth 512) "IR nesting budget")
                  (let [op (first body)
                        descend! #(body! f environment joins % (inc depth))]
                    (case op
                      "vdecl"
                      (let [[_ binder _ expression next] body i (get binder "idx")
                            key (variable-key f i) recipe (expression! environment expression)]
                        (define! key recipe)
                        (body! f (assoc environment i key) joins next (inc depth)))
                      "jdecl"
                      (let [[_ binder parameters inner next] body j (get binder "idx")
                            keys (mapv #(variable-key f (get-in % ["x" "idx"])) parameters)
                            joins (assoc joins j keys)
                            inner-env (into environment (map (fn [p key] [(get-in p ["x" "idx"]) key]) parameters keys))]
                        (doseq [key keys] (define! key {:dependencies []}))
                        (body! f inner-env joins inner (inc depth))
                        (body! f environment joins next (inc depth)))
                      "jmp"
                      (let [[_ binder arguments] body keys (get joins (get binder "idx"))]
                        (need! (and keys (= (count keys) (count arguments))) "join scope/arity")
                        (doseq [[key argument] (map vector keys arguments)]
                          (append! key (argument-key environment argument))))
                      "case" (doseq [alternative (nth body 4)] (descend! (last alternative)))
                      "ret" (append! (return-key f) (argument-key environment (nth body 1)))
                      ("inc" "dec") (descend! (nth body 5))
                      "del" (descend! (nth body 2))
                      ("set" "uset") (descend! (nth body 4))
                      "sset" (descend! (nth body 6))
                      "setTag" (descend! (nth body 3))
                      "unreachable" nil
                      (refuse! (str "body " op)))))]
          (doseq [[f d] declarations]
            (let [environment (into {} (map-indexed (fn [i p] [(get-in p ["x" "idx"]) (parameter-key f i)]) (get d "xs")))]
              (body! f environment {} (get d "body") 0))))
        ;; This rechecks native entry structure and its exact original rows;
        ;; parameter-domain claims supplied independently are never trusted.
        (doseq [e entries]
          (tick!) (entry/validate-rows! e by-name)
          (let [profile (get-in e ["typeCheck" "signature"])
                descriptor (if (string? profile) (signature/from-legacy profile) profile)
                arguments (get descriptor "arguments")
                plan (if (string? profile)
                       (cond-> (mapv #(hash-map "kind" "argument" "index" %) (range (count arguments)))
                         (= "io" (get descriptor "effect"))
                         (conj {"kind" "io-world" "representation" "canonical-erased-zero"}))
                       (get e "argumentPlan"))
                callable (get-in e ["callable" "name"])]
            (doseq [[i slot] (map-indexed vector plan)]
              (let [key [callable :host i]
                    kind (get slot "kind")
                    safe? (or (= "io-world" kind)
                              (and (= "argument" kind)
                                   (contains? managed-host-kinds (get (get arguments (get slot "index")) "kind"))))]
                (define! key (if safe? {:anchor true} {:unsupported "host heap leaf argument"}))
                (append! (parameter-key callable i) key)))))
        ;; Initialization invokes the raw action with its erased world.
        (doseq [f (set (keep #(get-in % ["runtime" "initializer"]) rows))
                [i parameter] (map-indexed vector (get-in declarations [f "xs"]))]
          (let [key [f :startup i]]
            (define! key (if (= "void" (get parameter "ty")) {:anchor true}
                          {:unsupported "initializer parameter"}))
            (append! (parameter-key f i) key)))
        (need! (not-any? debug @paps) "partial diagnostic application")
        (let [reachable
              (loop [pending (vec @seeds) visited #{}]
                (if (empty? pending) visited
                  (let [key (peek pending) pending (pop pending)]
                    (tick!)
                    (if (contains? visited key) (recur pending visited)
                      (let [recipe (get @recipes key)]
                        (need! recipe "unknown value origin")
                        (when-let [reason (:unsupported recipe)] (refuse! reason))
                        (when-let [f (:parameter recipe)] (swap! required-parameters conj f))
                        (need! (or (:anchor recipe) (seq (:dependencies recipe))) "unrooted value origin")
                        (recur (into pending (:dependencies recipe)) (conj visited key)))))))
              ;; All reachable origins must be supported. Additionally every
              ;; recursive component needs an established carrier boundary;
              ;; merely revisiting an obligation never proves it.
              productive
              (loop [known (set (filter #(:anchor (get @recipes %)) reachable))]
                (let [next (reduce (fn [result key]
                                     (tick!)
                                     (if (some known (:dependencies (get @recipes key))) (conj result key) result))
                                   known reachable)]
                  (if (= next known) known (recur next))))]
          (need! (= reachable productive) "recursive provenance without managed boundary")
          (need! (not-any? @required-parameters @paps)
                 "partial application exposes a constrained function"))))
    requirements))
