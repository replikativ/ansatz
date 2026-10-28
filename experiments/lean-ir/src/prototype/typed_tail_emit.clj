(ns prototype.typed-tail-emit
  "Bounded primitive trampoline emission from represented Pattern operations.
   This namespace retains no World, code catalogue, or arbitrary compiler options.")

(def ^:private generation (Object.))
(defn generation-token [] generation)
(defn compiler-token [] generation)

(defn- refuse! [reason]
  (throw (ex-info "Typed tail emission budget" {:typed-tail-emission-fallback reason})))

(defn- check-representation! [region names]
  (let [scalars #{"uint8" "uint16" "uint32" "uint64" "usize"}
        nats #{"tagged" "tobject"}
        nat? (= "lean-represented-tail/2" (:schema region))
        invalid! #(throw (ex-info "Invalid represented tail proof" {:typed-tail-invalid-representation true}))
        repr? (fn [x] (and (vector? x) (= 3 (count x)) (= :repr (first x))
                           (or (and (scalars (second x)) (= :long-bits (nth x 2)))
                               (and nat? (nats (second x)) (= :nonnegative-long (nth x 2))))))
        intrinsic? (fn [repr domain operation carrier]
                     (and (repr? repr)
                          (case domain
                            :unsigned64 (case operation
                                          :eq (and (= "uint8" (second repr)) (= [:carrier :long] carrier))
                                          (:add :sub) (and (#{"uint64" "usize"} (second repr))
                                                           (= [:carrier :unsigned-bigint] carrier)) false)
                            :nat (and nat? (= [:carrier :long] carrier)
                                      (case operation :eq (= "uint8" (second repr))
                                            (:add :sub) (nats (second repr)) false))
                            false)))]
    (when-not (contains? #{"lean-represented-tail/1" "lean-represented-tail/2"} (:schema region)) (invalid!))
    (doseq [name names :let [f (get-in region [:functions name]) table (:representations f)]]
      (letfn [(local! [id repr]
                (when-not (and (repr? repr)
                               (or (not nat?)
                                   (let [entry (get table id)]
                                     (and (= (:ir-type entry) (second repr)) (= (:lane entry) (nth repr 2))
                                          (= (:domain entry) (if (nats (second repr)) :nat-integer :unsigned-integer)))))) (invalid!)))]
        (doseq [{:keys [id type]} (:params f)]
          (local! id [:repr type (if (nats type) :nonnegative-long :long-bits)])
          (when (and nat? (not= (get-in table [id :proof])
                                         (if (nats type) {:kind :entry-guard :carrier :long :range [0 Long/MAX_VALUE]}
                                             {:kind :entry-guard :carriers [:long :bigint]}))) (invalid!)))
        (doseq [block (:blocks f) :let [op (:operation block)]]
          (when-not
           (and (vector? op)
                (case (first op)
                  :literal (and (= 6 (count op)) (repr? (nth op 3)) (= [:carrier :literal] (nth op 5))
                                (or (not (nats (second (nth op 3))))
                                    (and (= Long (class (nth op 4))) (<= 0 (nth op 4)))))
                  :intrinsic (and (= 9 (count op)) (intrinsic? (nth op 3) (nth op 4) (nth op 5) (nth op 8)))
                  :tail-intrinsic (and (= 8 (count op)) (intrinsic? (nth op 2) (nth op 3) (nth op 4) (nth op 7)))
                  :rc (and nat? (= 9 (count op)) (#{:inc :dec} (nth op 2))
                           (integer? (nth op 4)) (<= 0 (nth op 4) Integer/MAX_VALUE)
                           (boolean? (nth op 5)) (boolean? (nth op 6))
                           (= [:proof :nonreference] (nth op 8)) (repr? (nth op 7)))
                  :case (and (= 5 (count op)) (= :long-bits (nth op 4)))
                  :tail (and (= 5 (count op)) (= :simultaneous-carriers (nth op 4)))
                  :return (and (= 4 (count op)) (= [:carrier :propagate] (nth op 3))) false)) (invalid!))
          (case (first op)
            :literal (do (local! (nth op 2) (nth op 3))
                         (when (and nat? (not= (get-in table [(nth op 2) :proof])
                                              {:kind :literal :carrier (if (nats (second (nth op 3))) :long :literal)
                                               :value (nth op 4) :class (.getName (class (nth op 4)))})) (invalid!)))
            :intrinsic (do (local! (nth op 2) (nth op 3))
                           (when nat?
                             (let [descriptor (get-in region [:descriptors (nth op 6)])
                                   proof (get-in table [(nth op 2) :proof])]
                               (when-not (= proof {:kind :intrinsic :domain (nth op 4) :extern (:extern descriptor)
                                                   :carrier (second (nth op 8))
                                                   :condition (if (and (= :nat (nth op 4)) (= :add (nth op 5)))
                                                                :checked-small-add :unconditional)}) (invalid!)))))
            :rc (local! (nth op 3) (nth op 7))
            nil)
          (when (and nat? (contains? #{:intrinsic :tail-intrinsic} (first op)))
            (let [[domain args] (if (= :intrinsic (first op)) [(nth op 4) (nth op 7)] [(nth op 3) (nth op 6)])]
              (when (and (= :nat domain) (not (every? #(= :nonnegative-long (get-in table [(second %) :lane])) args))) (invalid!)))))))))

(defn- check-form!
  "Bound the realized form as well as graph expansion. Walk iteratively so a
   refusal itself does not depend on compiler or reader recursion limits."
  [form]
  (let [pending (java.util.ArrayDeque.) constants (java.util.HashSet.)]
    (.add pending form)
    (loop [work 0]
      (when (> work 100000) (refuse! :realized-form-budget))
      (when (> (.size constants) 12000) (refuse! :constant-pool-budget))
      (when-not (.isEmpty pending)
        (let [x (.removeLast pending)]
          (if (coll? x)
            (doseq [v x] (when (some? v) (.addLast pending v)))
            (.add constants x))
          (recur (inc work)))))))

(defn emit-factory [region names literal-tags options]
  (check-representation! region names)
  (let [machine (gensym "machine") context (gensym "context") initial (gensym "initial")
        safe (gensym "safe") fuel (gensym "fuel") limit (gensym "limit") one (gensym "one")
        registers (with-meta (gensym "registers") {:tag 'objects}) tag (gensym "tag") remaining (gensym "remaining")
        completed (gensym "completed") peak (gensym "peak") chunks (gensym "chunks") depth (gensym "caller_depth")
        width (reduce max 0 (map #(count (get-in region [:functions % :params])) names))
        lanes (mapv (fn [_] [(gensym "bits") (gensym "carrier")]) (range width))
        tags (zipmap names (range))
        construction (atom 0)
        emitted (atom 0)
        emission-limit (get-in region [:budgets :max-emission])]
    (letfn [(spend! [units]
              ;; Conservative form-node units, charged BEFORE building expanded
              ;; forms. Shared CFG suffixes may each materialize a full local
              ;; environment, so a graph-node bound alone is insufficient.
              (when (> (swap! construction + units) 100000)
                (refuse! :construction-budget)))
            (scalar [{:keys [bits carrier]}]
              `(prototype.typed-tail-execution/scalar-value ~context ~bits ~carrier))
            (operand [env x] (or (get env (second x))
                                 (throw (ex-info "Missing represented operand" {:operand x}))))
            (arguments [f env] (mapv #(scalar (get env (:id %))) (:params f)))
            (entry-exit [name f entry-env interpreted?]
              (spend! (+ 256 (* 32 (count (:params f)))))
              `(do
                 (prototype.mutable/materialize-tail-entry!
                  ~machine (nth (:names ~context) ~(get tags name)) ~(arguments f entry-env) ~completed ~peak)
                 ~(if interpreted?
                    `(do (if ~one (prototype.mutable/step! ~machine)
                             (prototype.mutable/run! ~machine (- ~fuel ~completed))) :interpreted)
                    :specialized)))
            (intrinsic [domain operation args env]
              (let [[a b] (map #(-> (operand env %) :bits) args)]
                (case operation
                  :add `(unchecked-add ~a ~b)
                  :sub (if (= domain :nat) `(long (if (< ~a ~b) 0 (unchecked-subtract ~a ~b))) `(unchecked-subtract ~a ~b))
                  :eq `(long (if (== ~a ~b) 1 0))
                  (throw (ex-info "Unsupported represented intrinsic" {:operation operation})))))
            (emit [name f id env entry-env cost local-peak]
              ;; Nested lexical lets and branch expansions consume JVM compiler
              ;; stack even when the represented graph is itself compact.
              (when (> cost 192) (refuse! :method-depth-budget))
              (when (> (swap! emitted inc) (* (count names) emission-limit))
                (refuse! :emission-budget))
              (spend! 64)
              (let [block (get-in f [:blocks id]) op (:operation block)
                    next-id (first (:successors block))]
                (case (first op)
                  :literal
                  (let [[_ _ dest _ value] op b (gensym "literal") c (gensym "recipe")]
                    `(let [~b (long ~(.longValue ^Number value))
                           ~c (long ~(get literal-tags [name id]))]
                       ~(emit name f next-id (assoc env dest {:bits b :carrier c}) entry-env (inc cost) local-peak)))

                  :intrinsic
                  (let [[_ _ dest _ domain operation _ args] op b (gensym "intrinsic") c (gensym "recipe")
                        success `(let [~b ~(intrinsic domain operation args env) ~c (long ~(if (or (= domain :nat) (= operation :eq)) 0 1))]
                                   ~(emit name f next-id (assoc env dest {:bits b :carrier c}) entry-env (+ cost 3) 1))]
                    (if (and (= domain :nat) (= operation :add))
                      (let [[a b] (map #(-> (operand env %) :bits) args)]
                        `(if (<= ~a (unchecked-subtract Long/MAX_VALUE ~b)) ~success ~(entry-exit name f entry-env true)))
                      success))

                  :rc
                  (do (operand env [:var (nth op 3)])
                      (emit name f next-id env entry-env (inc cost) local-peak))

                  :case
                  (let [[_ _ args alternatives] op
                        _ (spend! (+ 128 (* 32 (count alternatives))))
                        b (:bits (operand env (first args)))
                        default (some #(when (= :default (first %)) (second %)) alternatives)
                        choices (remove #(= :default (first %)) alternatives)]
                    `(cond
                       ~@(mapcat (fn [[v target]] [`(== ~b (long ~v))
                                                  (emit name f target env entry-env (inc cost) local-peak)]) choices)
                       :else ~(if (some? default)
                                (emit name f default env entry-env (inc cost) local-peak)
                                (entry-exit name f entry-env true))))

                  :tail
                  (let [[_ _ target args] op
                        _ (spend! (+ 128 (* 32 width)))
                        values (mapv #(operand env %) args) n (inc cost)]
                    `(recur (long ~(get tags target))
                            ~@(mapcat (fn [i] (if-let [v (get values i)] [(:bits v) (:carrier v)] [`(long 0) `(long 0)])) (range width))
                            (unchecked-subtract ~remaining (long ~n))
                            (unchecked-add ~completed (long ~n))
                            (long (max ~peak (unchecked-add ~depth (long ~local-peak))))
                            (unchecked-inc ~chunks)))

                  :return
                  (let [[_ _ args] op
                        _ (spend! (+ 256 (* 32 (+ (count env) (count (:params f))))))
                        locals (mapv (fn [[id v]] `[~id ~(scalar v)]) (sort-by key env))]
                    `(do
                       (prototype.mutable/materialize-tail-return!
                        ~machine (nth (:names ~context) ~(get tags name)) ~(arguments f entry-env)
                        (prototype.typed-tail-execution/return-body ~context (nth (:names ~context) ~(get tags name)) ~(:pc block))
                        ~locals ~(scalar (operand env (first args)))
                        (unchecked-add ~completed (long ~(inc cost))) (long (max ~peak (unchecked-add ~depth (long ~local-peak)))))
                       :specialized))

                  :tail-intrinsic
                  (let [[_ _ _ domain operation target args] op b (gensym "result") c (gensym "recipe")
                        dependency (get-in region [:dependencies target]) params (:params dependency)
                        _ (spend! (+ 384 (* 64 (count args)) (* 32 (count params))))
                        result {:bits b :carrier c}
                        values (mapv #(scalar (operand env %)) args)
                        target-tag (gensym "target") body (gensym "body")
                        target-locals (conj (mapv (fn [id value] `[~id ~value]) params values)
                                            `[(second ~body) ~(scalar result)])]
                    (let [success `(let [~b ~(intrinsic domain operation args env) ~c (long ~(if (or (= domain :nat) (= operation :eq)) 0 1))
                           ~target-tag '~target ~body (get-in (:dependencies ~context) [~target-tag :body])]
                       (prototype.mutable/materialize-tail-return!
                        ~machine ~target-tag ~values (nth ~body 3) ~target-locals ~(scalar result)
                        (unchecked-add ~completed (long ~(+ cost 3))) (long (max ~peak (unchecked-add ~depth (long ~local-peak)))))
                       :specialized)]
                      (if (and (= domain :nat) (= operation :add))
                        (let [[a b] (map #(-> (operand env %) :bits) args)]
                          `(if (<= ~a (unchecked-subtract Long/MAX_VALUE ~b)) ~success ~(entry-exit name f entry-env true)))
                        success)))
                  (throw (ex-info "Unsupported represented operation" {:operation (first op)})))))
            (arm [i name]
              (spend! 128)
              (let [f (get-in region [:functions name])
                    env (into {} (map (fn [p [b c]] [(:id p) {:bits b :carrier c}]) (:params f) lanes))]
                `(cond
                   (>= ~chunks (max (long 1) (long ~limit))) ~(entry-exit name f env false)
                   (< ~remaining (long ~(:max-cost f))) ~(entry-exit name f env true)
                   :else ~(emit name f (:entry f) env env 0 0))))
            (initial-value [i]
              (spend! (+ 32 (* 32 (count names))))
              `(case (long ~initial)
                 ~@(mapcat (fn [[j name]]
                             [j (if-let [p (get (get-in region [:functions name :params]) i)]
                                  `(aget ~registers (int ~(:id p))) `(Long/valueOf 0))])
                           (map-indexed vector names))))]
      (spend! (+ 512 (* 64 width)))
      (let [form `(fn [~machine ~context ~initial ~safe ~fuel ~limit ~one]
                    (let [~registers (prototype.mutable/locals-array ~machine)
                          ~depth (long (prototype.mutable/tail-frame-depth ~machine))]
                      (loop [~tag (long ~initial)
                             ~@(mapcat (fn [i [b c]]
                                         ;; Hint a local: metadata on the `case`
                                         ;; receiver is lost during macroexpansion.
                                         ;; Number.longValue preserves UInt64 bits
                                         ;; for BigInt inputs above Long/MAX_VALUE.
                                         (let [value (with-meta (gensym "entry_scalar") {:tag 'java.lang.Number})]
                                           [b `(let [~value ~(initial-value i)] (.longValue ~value))
                                            c `(long (if (= Long (class ~(initial-value i))) 0 1))])) (range width) lanes)
                             ~remaining (long ~safe) ~completed (long 0) ~peak (long ~depth) ~chunks (long 0)]
                        (case ~tag
                          ~@(mapcat (fn [[i name]] [i (arm i name)]) (map-indexed vector names))
                          (throw (ex-info "Invalid typed-tail tag" {}))))))]
        (check-form! form)
        (binding [*ns* (the-ns 'prototype.typed-tail-execution)
                  *compiler-options* (assoc *compiler-options* :direct-linking (boolean (:direct-linking options)))]
          {:code (eval form) :form form})))))
