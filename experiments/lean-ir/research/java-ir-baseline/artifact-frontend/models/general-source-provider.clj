(ns general-frontend-source-provider-models-v1
  "Real tiny Java Nodes with layout-faithful Syntax/scope models. These are NOT
   original parser outputs, authenticated Source receipts or gate capabilities."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [general-frontend-source-provider-v1 :as provider])
  (:import [java.util IdentityHashMap]))
(def ^:dynamic *basis* nil)
(defn seam [name] (ns-resolve 'general-frontend-source-provider-v1 name))
(defn captured [text]
  {:text text :byte-count (alength (.getBytes ^String text "UTF-8")) :sha256 ((seam 'hash-text) text)
   :path (java.nio.file.Path/of "Model.lean" (make-array String 0)) :module ["Model"]})
(defn kind [leaf] (sp/typed-name (str "Lean.Parser.Command." leaf)))
(defn node [leaf & args] {:kind (kind leaf) :args (vec args)})
(defn declaration [& args] (node "declaration" {:kind ["anonymous"] :args []} (apply node "definition" args)))
(defn install! [build text]
  (let [ctx (j/prepare-host-program *basis* [] []) source (j/source-binding ctx (Object.))
        nodes (atom []) next-id (atom 0) memo (atom {})
        allocate (fn [kind tag fields scalars]
                   (let [id (swap! next-id inc)]
                     (swap! nodes conj (j/graph-node ctx (cond-> {:kind kind :id id :fields fields}
                                                          (= kind :ctor) (assoc :tag tag :scalars scalars))))
                     (j/graph-ref ctx id)))]
    (letfn [(ctor [tag fields scalars] (allocate :ctor tag fields scalars))
            (array [fields] (allocate :array nil fields []))
            (name [n]
              (or (get @memo n)
                  (let [out (if (= ["anonymous"] n) 0
                              (ctor (if (= "str" (first n)) 1 2) [(name (second n)) (nth n 2)] (repeat 8 0)))]
                    (swap! memo assoc n out) out)))
            (syntax [model]
              (cond
                (= :missing model) 0
                (:atom model) (ctor 2 [2 (:atom model)] [])
                :else (let [info (if-let [[a b] (:range model)] (ctor 1 [a b] [1]) 2)]
                        (ctor 1 [info (name (:kind model)) (array (mapv syntax (:args model)))] []))))]
      (let [ref (build {:ctor ctor :array array :name name :syntax syntax}) engine (j/machine ctx)
            graph (j/selected-owner-graph ctx source (Object.) @nodes [] [] [ref])
            root (first (j/install-graph! ctx engine graph))
            s {:driver {:engine engine :current-ctx (atom ctx)}}]
        {:ctx ctx :engine engine :root root :p {:frontend s :capture ((seam 'capture-source) (captured text))}}))))
(defn syntax-fixture [model] (install! #((:syntax %) model) "α\n"))
(defn policy [fixture] ((seam 'syntax-policy!) (:p fixture) (:root fixture)))
(defn rejects? [f] (try (f) false (catch Exception _ true)))
(defmacro with-fixture [[binding expression] & body]
  `(let [~binding ~expression]
     (try ~@body (finally (j/close! (:ctx ~binding) (:engine ~binding))))))

(deftest ordinary-syntax-is-not-a-source-body-whitelist
  (doseq [form [(declaration {:atom "set_option is just literal model text"})
                (node "namespace") (node "section") (node "end")
                (node "declaration" {:kind ["anonymous"] :args []} (node "theorem"))
                (node "declaration" {:kind ["anonymous"] :args []} (node "axiom"))]]
    (with-fixture [f (syntax-fixture form)]
      (is (= :command (:kind (policy f))))))
  (doseq [[leaf result] [["eoi" :eoi] ["exit" :exit] ["import" :import]]]
    (with-fixture [f (syntax-fixture (node leaf))]
      (is (= result (:kind (policy f)))))))

(deftest nested-option-attribute-and-meta-effects-are-rejected-before-reply
  (doseq [label ["Lean.Parser.Command.set_option" "Lean.Parser.Term.set_option" "Lean.Parser.Tactic.set_option"
                 "Lean.Parser.Command.unlock_limits" "Lean.Parser.Term.attributes" "Lean.Parser.Term.attrInstance"
                 "Lean.Parser.Command.meta" "Lean.Parser.Command.unsafe" "Lean.Parser.Command.partial"
                 "Lean.Parser.Command.initialize" "Lean.Parser.Tactic.runTac"]]
    (with-fixture [f (syntax-fixture (declaration {:kind (sp/typed-name label) :args []}))]
      (let [before (.instructionCount (:engine f))]
        (is (rejects? #(policy f)))
        (is (= before (.instructionCount (:engine f))))))))

(deftest custom-command-opaque-block-and-display-name-spoofing-rejected
  (doseq [form [(node "opaque") (node "initialize") (node "attribute")
                {:kind ["str" ["anonymous"] "Lean.Parser.Command.namespace"] :args []}
                {:kind (sp/typed-name "Custom.command") :args []}
                (node "declaration" {:kind ["anonymous"] :args []} (node "inductive"))
                (node "declaration" {:kind ["anonymous"] :args []} (node "opaque"))]]
    (with-fixture [f (syntax-fixture form)] (is (rejects? #(policy f))))))

(deftest captured-utf8-positions-and-invalid-inputs
  (let [p {:capture ((seam 'capture-source) (captured "α\n"))}]
    (is (= 3 (get-in p [:capture :byte-count])))
    (is (= [0 3 3] (get-in p [:capture :line-starts])))
    (doseq [position [0 2 3]] (is (= position ((seam 'position!) p position))))
    (doseq [position [1 -1 4 (biginteger 2)]] (is (rejects? #((seam 'position!) p position))))
    (is (rejects? #((seam 'capture-source) (assoc (captured "α") :byte-count 1))))
    (is (rejects? #((seam 'capture-source) (assoc (captured "x") :sha256 (apply str (repeat 64 "0"))))))))

(deftest missing-deep-and-out-of-source-syntax-is-rejected
  (doseq [form [(declaration :missing)
                (declaration (nth (iterate #(hash-map :kind ["anonymous"] :args [%]) {:atom "x"}) 258))
                (assoc (node "namespace") :range [1 2])
                (assoc (node "namespace") :range [0 4])]]
    (with-fixture [f (syntax-fixture form)] (is (rejects? #(policy f)))))
  (with-fixture [f (syntax-fixture (node "namespace" {:atom "x"}))]
    ;; Unsafe model mutation solely isolates actual read-only cycle rejection;
    ;; no original parser or source capability is claimed for this graph.
    (let [s (get-in f [:p :frontend]) root-fields (sp/fields s (:root f))
          args (aget ^objects root-fields 2) fields ^objects (sp/fields s args) old (aget fields 0)]
      (try (aset fields 0 (:root f)) (is (rejects? #(policy f)))
           (finally (aset fields 0 old))))))

(deftest namespace-scopes-preserve-protected-options-and-empty-attributes
  (with-fixture [f (install! (fn [{:keys [ctor array name]}]
                              (let [opts (ctor 0 [0] [0]) empty (array [])
                                    scope (fn [header ns options flags]
                                            (ctor 0 [header options ns 0 0 empty empty 0 0 0] flags))
                                    outer (scope "" 0 opts [0 0 0]) inner (scope "N" (name (sp/typed-name "N")) opts [0 0 0])
                                    scopes (ctor 1 [inner (ctor 1 [outer 0] [])] [])]
                                (ctor 0 [0 0 scopes 0 0 0 0 0 0 0 0] []))) "α\n")]
    (let [s (get-in f [:p :frontend]) cf (sp/fields s (:root f))
          cons1 (aget ^objects cf 2) scope (aget ^objects (sp/fields s cons1) 0)
          sf ^objects (sp/fields s scope) opts (aget sf 1)
          p (assoc (:p f) :frozen-options ((seam 'frozen) s opts))]
      (is (identical? opts (:options ((seam 'scope-view) p (:root f)))))
      (is (= 0 (:environment ((seam 'scope-view) p (:root f)))))
      (let [original (aget sf 9)]
        (try (aset sf 9 scope) (is (rejects? #((seam 'scope-view) p (:root f)))) (finally (aset sf 9 original))))
      (is (rejects? #((seam 'scope-view) (assoc p :frozen-options [:changed]) (:root f)))))))

(deftest unissued-provider-and-gate-data-grant-no-authority
  (doseq [token [nil {} {:approved true} (provider/->Provider) (provider/->GateReceipt)]]
    (is (rejects? #(provider/callbacks token)))
    (is (rejects? #(provider/close! token)))))

(deftest observer-stamp-detects-owner-effects-and-does-not-claim-rollback
  (with-fixture [f (syntax-fixture (node "namespace"))]
    (let [p (:p f)]
      (is (= 42 ((seam 'readonly) p (constantly 42))))
      (is (rejects? #((seam 'readonly) p (fn [] (j/retain! (:ctx f) (:engine f) (:root f)))))))))

(defn check! [basis]
  (binding [*basis* basis] (run-tests 'general-frontend-source-provider-models-v1)))
