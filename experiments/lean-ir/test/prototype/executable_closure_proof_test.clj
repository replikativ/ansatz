(ns prototype.executable-closure-proof-test
  "Static assertion controls only; no World owners, Source, Init or guest execution."
  (:require [clojure.test :refer [deftest is]]
            [prototype.executable-closure-proof :as proof]
            [prototype.eval-const :as eval]
            [prototype.import-ir :as ir])
  (:import [java.lang.ref WeakReference]
           [java.util WeakHashMap ArrayList HashMap]
           [java.lang.reflect Modifier]
           [prototype.executable_closure_proof ExecutableClosureProof]))

(defn semantic-vars []
  [#'eval/validate-executables! #'eval/check-function-closure! #'eval/executable-dependencies
   #'ir/static-targets #'ir/static-targets-canonical #'ir/frozen-target?
   #'ir/canonical-target #'ir/frozen-target-scalar-classes
   #'ir/static-targets-tree #'ir/static-targets-shared #'ir/terminal-static-ops
   #'proof/ordinary-map? #'proof/frozen-sequence? #'proof/target-cost
   #'proof/freeze-target #'proof/freeze-roots #'proof/stable-closure?])

(defn program []
  (let [leaf {:params [] :body [:return [:imm 42]]}
        root {:params [] :body [:tail [:direct "leaf"] []]}
        functions {"root" root "leaf" leaf}]
    {:world {:functions functions} :registry functions :roots ["root"]}))
(defn check [{:keys [world registry roots]} previous] (proof/validate! world registry roots previous))
(defn counting [f]
  (let [calls (atom 0) original eval/validate-executables!]
    (with-redefs [eval/validate-executables! (fn [& args] (swap! calls inc) (apply original args))]
      (f calls))))

(deftest cold-validation-precedes-issuance-and-hit-does-no-closure-validation
  (counting
    (fn [calls]
      (let [input (program) issued (check input nil)]
        (is issued)
        (is (= 1 @calls))
        (doseq [_ (range 20)] (is (identical? issued (check input issued))))
        (is (= 1 @calls))
        (is (not (identical? issued (check (assoc input :roots ["leaf"]) issued))))
        (is (= 2 @calls))
        (is (thrown? clojure.lang.ExceptionInfo (check (assoc input :roots ["missing"]) issued)))
        (is (= 3 @calls))))))

(deftest each-image-registry-and-root-selection-change-requires-full-validation
  (counting
    (fn [calls]
      (let [input (program) issued (check input nil)]
        (doseq [changed [(update-in input [:world :functions] with-meta {:new-image true})
                         (update input :registry with-meta {:new-registry true})
                         (assoc input :roots ["root" "leaf"])
                         (assoc input :roots ["root" "root"])]]
          (is (not (identical? issued (check changed issued)))))
        (is (= 5 @calls))
        (let [changed (assoc-in input [:world :functions "leaf"] {:params [] :body [:return [:imm 9]]})]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"differs from authorized" (check changed issued)))
          (is (some? (check (assoc changed :registry (get-in changed [:world :functions])) issued))))))))

(deftest metadata-bearing-name-spines-are-uncached-and-outer-root-metadata-is-not-retained
  (let [owner (Object.) clean ["str" ["anonymous"] "root"]
        decorated [(with-meta clean {:owner owner})
                   ["str" (with-meta ["anonymous"] {:owner owner}) "root"]
                   (with-meta ["str" (with-meta ["anonymous"] {:owner owner}) "root"] {:owner owner})]
        function {:params [] :body [:return [:imm 42]]}
        ;; A map key's metadata stays behind a weak map reference. It must never
        ;; be copied into the proof's strong root vector via an equal lookup key.
        functions {(first decorated) function}
        roots (with-meta [clean] {:owner owner})
        input {:world {:functions functions :owner owner} :registry functions :roots roots}
        issued (check input nil) frozen (.-roots ^ExecutableClosureProof issued)]
    (is issued)
    (is (= [clean] frozen))
    (is (not (identical? roots frozen)))
    (is (nil? (meta frozen)))
    (is (nil? (meta (first frozen))))
    (is (nil? (meta (second (first frozen)))))
    (is (identical? issued (check (assoc input :roots (list clean)) issued)))
    (doseq [name decorated]
      (is (nil? (check (assoc input :roots [name]) nil)))
      (is (nil? (check (assoc input :roots [name]) issued))))))

(deftest mutable-root-containers-and-targets-keep-the-original-uncached-path
  (let [input (program) mutable (ArrayList. ["root"])]
    (is (nil? (check (assoc input :roots mutable) nil)))
    (.set mutable 0 "missing")
    (is (thrown? clojure.lang.ExceptionInfo (check (assoc input :roots mutable) nil))))
  (let [target (ArrayList. ["mutable-name"]) function {:params [] :body [:return [:imm 42]]}
        functions {target function}]
    (is (nil? (proof/validate! {:functions functions} functions [target] nil)))))

(deftest mutable-body-and-runtime-dependencies-never-mint-a-proof
  (let [body (ArrayList. [:tail [:direct "leaf"] []])
        input (program) function (assoc (get-in input [:world :functions "root"]) :body body)
        functions (assoc (:registry input) "root" function)]
    (is (nil? (proof/validate! {:functions functions} functions ["root"] nil)))
    (.set body 1 [:direct "missing"])
    (is (thrown? clojure.lang.ExceptionInfo (proof/validate! {:functions functions} functions ["root"] nil))))
  (doseq [dependencies [(ArrayList. ["leaf"]) (map identity ["leaf"])]]
    (let [input (program) function {:params [] :body [:return [:imm 1]] :runtime-dependencies dependencies}
          functions (assoc (:registry input) "root" function)]
      ;; Java List is already rejected by the original validator; lazy Clojure
      ;; dependencies may validate but must never become cached evidence.
      (if (instance? ArrayList dependencies)
        (is (thrown? clojure.lang.ExceptionInfo (proof/validate! {:functions functions} functions ["root"] nil)))
        (is (nil? (proof/validate! {:functions functions} functions ["root"] nil)))))))

(deftest supported-immutable-dependencies-and-unread-literals-remain-eligible
  (doseq [dependencies [["leaf"] #{"leaf"} (list "leaf") '()]]
    (let [input (program) payload (ArrayList. ["not-code"])
          function {:params [] :body [:return [:imm payload]] :runtime-dependencies dependencies}
          functions (assoc (:registry input) "root" function)
          issued (proof/validate! {:functions functions} functions ["root"] nil)]
      (is issued)
      (.set payload 0 "changed-literal")
      (is (identical? issued (proof/validate! {:functions functions} functions ["root"] issued))))))

(deftest unrelated-mutable-keys-and-exotic-maps-remain-uncached
  (let [input (program) mutable (ArrayList. ["key"])
        functions (assoc (:registry input) mutable :unrelated)]
    (is (nil? (proof/validate! {:functions functions} functions ["root"] nil)))
    (.set mutable 0 "changed-hash")
    (is (nil? (proof/validate! {:functions functions} functions ["root"] nil))))
  (let [input (program) mutable (ArrayList. ["unrelated-key"])
        functions (assoc (into (:registry input) (for [i (range 20)] [(str "padding" i) {:params [] :body [:return [:imm 0]]}]))
                         mutable :unrelated)]
    (is (= clojure.lang.PersistentHashMap (class functions)))
    (is (nil? (proof/validate! {:functions functions} functions ["root"] nil)))
    (.set mutable 0 "new-hash")
    (is (nil? (proof/validate! {:functions functions} functions ["root"] nil))))
  (let [input (program) sorted (into (sorted-map) (:registry input))]
    (is (nil? (proof/validate! {:functions sorted} sorted ["root"] nil))))
  (let [function (HashMap. { :params [] :body [:return [:imm 42]]}) functions {"root" function}]
    (is (nil? (proof/validate! {:functions functions} functions ["root"] nil)))))

(deftest forged-proofs-and-new-epochs-cannot-grant-a-hit
  (counting
    (fn [calls]
      (let [{:keys [world registry roots] :as input} (program)
            issued (check input nil)
            forged (ExecutableClosureProof. (WeakReference. (:functions world)) (WeakReference. registry)
                                             roots (.-rules ^ExecutableClosureProof issued))]
        (is (not (identical? forged (check input forged))))
        (is (= 2 @calls))
        (is (thrown? clojure.lang.ExceptionInfo
                     (check (assoc-in input [:world :functions "leaf"] {}) forged)))
        (with-redefs-fn {(ns-resolve 'prototype.executable-closure-proof 'issued) (WeakHashMap.)}
          #(let [replacement (check input issued)]
             (is (not (identical? issued replacement)))
             (is (identical? replacement (check input replacement)))))
        (is (= 4 @calls))))))

(deftest held-proofs-have-only-weak-maps-rules-and-frozen-roots
  (let [input (program) issued (check input nil)
        fields (remove #(Modifier/isStatic (.getModifiers ^java.lang.reflect.Field %))
                       (.getDeclaredFields (class issued)))]
    (is (= #{"functions" "registry" "roots" "rules"} (set (map #(.getName ^java.lang.reflect.Field %) fields))))
    (is (instance? WeakReference (.-functions ^ExecutableClosureProof issued)))
    (is (instance? WeakReference (.-registry ^ExecutableClosureProof issued)))
    (is (= clojure.lang.PersistentVector (class (.-roots ^ExecutableClosureProof issued))))
    (let [table @(ns-resolve 'prototype.executable-closure-proof 'issued)]
      (is (instance? WeakHashMap table))
      (locking table (is (every? true? (.values ^WeakHashMap table)))))
    (is (= (count (semantic-vars)) (count (.-rules ^ExecutableClosureProof issued))))
    (is (every? #(instance? WeakReference %) (.-rules ^ExecutableClosureProof issued)))
    ;; Seed INSIDE the stable instrumentation scope: changing a validator Fn
    ;; after issuance now correctly misses independently of weak-ref clearing.
    (doseq [slot (range (+ 2 (count (semantic-vars))))]
      (counting
        (fn [calls]
          (let [fresh (check input nil)
                references (into [(.-functions ^ExecutableClosureProof fresh) (.-registry ^ExecutableClosureProof fresh)]
                                 (.-rules ^ExecutableClosureProof fresh))]
            (.clear ^WeakReference (nth references slot))
            (is (not (identical? fresh (check input fresh))))
            (is (= 2 @calls))))))))


(deftest redefined-validation-or-dependency-rules-invalidate-otherwise-matching-proofs
  (doseq [rule (semantic-vars)]
    (counting
      (fn [calls]
        (let [input (program) issued (check input nil) original @rule
              replacement (if (fn? original) (fn [& args] (apply original args))
                              (with-meta original {:new-rule-value true}))]
          (with-redefs-fn {rule replacement}
            #(let [next-proof (check input issued)]
               (is next-proof)
               (is (not (identical? issued next-proof)))
               (is (= 2 @calls))
               (is (identical? next-proof (check input next-proof)))
               (is (= 2 @calls)))))))))

(deftest rule-changes-during-full-validation-prevent-issuance
  (let [input (program) full eval/validate-executables!
        walker #'eval/check-function-closure! original @walker
        replacement (fn [& args] (apply original args))]
    (with-redefs-fn
      {walker original
       #'eval/validate-executables!
       (fn [& args]
         (let [result (apply full args)]
           (alter-var-root walker (constantly replacement))
           result))}
      #(do
         (is (nil? (check input nil)))
         ;; Once that new semantic root is stable a new full check may issue.
         (is (some? (check input nil)))))))

(deftest tightening-an-eligibility-helper-cannot-reuse-a-previous-proof
  (counting
    (fn [calls]
      (let [input (program) issued (check input nil)]
        (with-redefs-fn {#'proof/ordinary-map? (constantly false)}
          #(is (nil? (check input issued))))
        (is (= 2 @calls))))))
