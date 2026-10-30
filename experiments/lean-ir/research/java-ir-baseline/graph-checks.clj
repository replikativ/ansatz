(ns java-ir-graph-checks
  "One-shot, all-persistent bootstrap graph import; no full frontend image."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [java-ir-generation-checks :as g]
            [java-ir-header-checks :as h]
            [java-ir-host-checks :as host]
            [java-ir-code-checks :as code]))
(def ^:dynamic *basis* nil)
(defn global-row [label]
  (assoc (c/decl label [] "object" ["unreachable"])
         :runtime {:role "initialized" :initializer (c/name-ir (str "init-" label))}))
(defn setup []
  (let [base (j/prepare-host-program *basis* [] []) source (j/source-binding base (Object.))
        global (h/header source (global-row "global"))
        identity (h/header source h/identity-row)]
    {:ctx (j/register-headers base [global identity]) :source source :global global :identity identity}))
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn recipe [ctx source nodes globals values roots]
  (j/prepared-graph ctx source (Object.) nodes globals values roots))

(deftest imported-global-aliases-cycles-and-ref-isolation-survive-fork
  (let [{:keys [ctx source global]} (setup) engine (j/machine ctx)
        ref1 (j/graph-ref ctx 1) ref2 (j/graph-ref ctx 2)
        graph (recipe ctx source [(j/graph-node ctx {:kind :ctor :id 1 :tag 7 :fields [ref2]})
                                   (j/graph-node ctx {:kind :ref :id 2 :fields [ref1]})]
                      [global] [ref1] [ref1 ref2 ref1])
        [ctor cell again] (j/install-graph! ctx engine graph)]
    (try
      (is (identical? ctor again))
      (is (identical? ctor (j/call ctx engine "global" [])))
      (is (identical? cell (aget ^objects (fields ctx ctor) 0)))
      (is (identical? ctor (aget ^objects (fields ctx cell) 0)))
      (is (= 0 (c/rc ctx ctor) (c/rc ctx cell)))
      (is (nil? (j/code-request ctx engine)))
      (let [{:keys [engine roots]} (j/fork! ctx engine [ctor cell]) child engine
            [child-ctor child-cell] roots]
        (try
          (is (not (identical? ctor child-ctor)))
          (is (identical? child-ctor (j/call ctx child "global" [])))
          (is (identical? child-cell (aget ^objects (fields ctx child-ctor) 0)))
          ;; Explicit host-side mutation; Ref.set execution is a later tranche.
          (aset ^objects (fields ctx child-cell) 0 42)
          (is (identical? ctor (aget ^objects (fields ctx cell) 0)))
          (is (= 42 (aget ^objects (fields ctx child-cell) 0)))
          (is (g/bad? #(j/install-graph! ctx child graph)))
          (finally (j/close! ctx child))))
      (is (g/bad? #(j/install-graph! ctx engine graph)))
      (is (identical? ctor (j/call ctx engine "global" [])))
      (is (= 1 (count (host/private-value engine "preparedGlobalSources"))))
      (finally (j/close! ctx engine)))))

(deftest imported-closure-uses-authentic-unforced-header-and-demanded-code
  (let [{:keys [ctx source identity]} (setup)
        ctx (j/extend-program ctx (x/raw [(second g/common)])) engine (j/machine ctx)
        graph (recipe ctx source [(j/graph-node ctx {:kind :closure :id 1 :target identity})]
                      [] [] [(j/graph-ref ctx 1)])
        [closure] (j/install-graph! ctx engine graph)
        ready (code/materialize ctx identity h/identity-row [])]
    (try
      (is (= 0 (c/rc ctx closure)))
      (is (nil? (aget (h/slots ctx) (j/function-id ctx "identity"))))
      (j/start! ctx engine "apply" [closure 42])
      (let [request (code/request! ctx engine)]
        (is (identical? identity (j/request-value request "header")))
        (j/resume-code! ready engine request)
        (is (= 42 (code/finish! ready engine))))
      (is (= 0 (c/rc ctx closure)))
      (finally (j/close! ready engine)))))

(deftest packed-scalars-and-array-fields-are-copied-before-publication
  (let [{:keys [ctx source]} (setup)
        ctx (j/extend-program ctx (x/raw [(c/decl "read" [(c/p 1 "object")] "uint32"
                              (c/let-ir 2 "uint32" {:sproj {:x {:idx 1} :n 1 :offset 0}} (c/ret 2)))]))
        engine (j/machine ctx) ref (j/graph-ref ctx 1)
        scalar (j/graph-node ctx {:kind :ctor :id 1 :tag 4 :fields [0] :scalars [-1 -1 -1 -1]})
        array (j/graph-node ctx {:kind :array :id 2 :fields [ref ref]})
        graph (recipe ctx source [scalar array] [] [] [(j/graph-ref ctx 2)])
        [a] (j/install-graph! ctx engine graph) node (aget ^objects (fields ctx a) 0)]
    (try
      (is (identical? node (aget ^objects (fields ctx a) 1)))
      (is (true? (host/private-value a "array")))
      (is (= 4294967295 (j/call ctx engine "read" [node])))
      (is (= 0 (c/rc ctx node) (c/rc ctx a)))
      (finally (j/close! ctx engine)))))

(deftest malformed-imports-leave-globals-and-one-shot-marker-unpublished
  (let [{:keys [ctx source global]} (setup) engine (j/machine ctx)
        ref #(j/graph-ref ctx %) node #(j/graph-node ctx %)
        valid (recipe ctx source [(node {:kind :ref :id 1 :fields [42]})] [global] [(ref 1)] [])]
    (try
      (doseq [build [#(recipe ctx source [(node {:kind :ref :id 1 :fields [(ref 99)]})] [global] [(ref 1)] [])
                     #(recipe ctx source [(node {:kind :ref :id 1 :fields [0]})
                                          (node {:kind :ref :id 1 :fields [0]})] [global] [(ref 1)] [])
                     #(recipe ctx source [(node {:kind :ref :id 1 :fields [0]})
                                          (node {:kind :ref :id 2 :fields [0]})] [global] [(ref 1)] [])
                     #(recipe ctx source [(node {:kind :ref :id 1 :rc 1 :fields [0]})] [global] [(ref 1)] [])
                     #(recipe ctx source [(node {:kind :ref :id 1 :fields [(Object.)]})] [global] [(ref 1)] [])
                     #(recipe ctx source [(node {:kind :ref :id 1 :fields [-1]})] [global] [(ref 1)] [])]]
        (is (g/bad? #(j/install-graph! ctx engine (build))))
        (is (false? (aget ^booleans (host/private-value engine "constantReady") (j/function-id ctx "global"))))
        (is (false? (host/private-value engine "graphInstalled"))))
      (j/install-graph! ctx engine valid)
      (is (= 42 (aget ^objects (fields ctx (j/call ctx engine "global" [])) 0)))
      (finally (j/close! ctx engine)))))

(deftest foreign-headers-and-complete-closures-are-not-import-authority
  (let [{:keys [ctx source identity]} (setup) engine (j/machine ctx)
        foreign (h/header (j/source-binding ctx (Object.)) h/identity-row)]
    (try
      (doseq [descriptor [{:kind :closure :id 1 :target foreign}
                          {:kind :closure :id 1 :target identity :fields [0]}]]
        (is (g/bad? #(j/install-graph! ctx engine
                           (recipe ctx source [(j/graph-node ctx descriptor)] [] [] [(j/graph-ref ctx 1)])))))
      (is (false? (host/private-value engine "graphInstalled")))
      (finally (j/close! ctx engine)))))

(deftest import-requires-idle-and-ref-cannot-be-used-as-constructor
  (let [{:keys [ctx source identity]} (setup)
        ctx (j/extend-program ctx (x/raw [(c/decl "project" [(c/p 1 "object")] "object"
                            (c/let-ir 2 "object" {:proj {:x {:idx 1} :i 0}} (c/ret 2)))]))
        engine (j/machine ctx)
        graph (recipe ctx source [(j/graph-node ctx {:kind :ref :id 1 :fields [42]})]
                      [] [] [(j/graph-ref ctx 1)])]
    (j/start! ctx engine "identity" [42])
    (is (g/bad? #(j/install-graph! ctx engine graph)))
    (is (false? (host/private-value engine "graphInstalled")))
    (let [ready (code/materialize ctx identity h/identity-row [])]
      (j/resume-code! ready engine (j/code-request ctx engine))
      (is (= 42 (code/finish! ready engine)))
      (let [[ref] (j/install-graph! ready engine graph)]
        (is (g/bad? #(j/call ready engine "project" [ref]))))
      ;; Failed guest-frame cleanup remains unsupported.
      (is (g/bad? #(j/close! ready engine))))))

(deftest bounded-recipes-and-facade-shapes-reject-before-publication
  (let [{:keys [ctx source identity]} (setup) engine (j/machine ctx)
        node (j/graph-node ctx {:kind :ref :id 1 :fields [0]})]
    (try
      (is (g/bad? #(recipe ctx source (repeat 100001 node) [] [] [])))
      (is (g/bad? #(j/graph-node ctx {:kind :ref :id 1 :fields [0 1]})))
      (is (g/bad? #(j/graph-node ctx {:kind :array :id 1 :fields [] :scalars [1]})))
      (is (g/bad? #(j/graph-node ctx {:kind :closure :id 1})))
      (is (some? (j/graph-node ctx {:kind :ctor :id 1 :tag 243 :fields [0]})))
      (is (g/bad? #(j/graph-node ctx {:kind :ctor :id 1 :tag 244 :fields [0]})))
      (is (g/bad? #(j/graph-node ctx {:kind :ctor :id 1 :tag 0 :fields (vec (repeat 256 0))})))
      (is (g/bad? #(j/graph-node ctx {:kind :ctor :id 1 :tag 0 :scalars (vec (repeat 1024 0))})))
      (is (false? (host/private-value engine "graphInstalled")))
      (is (identical? identity
             (get {(c/name-ir "identity") identity}
                  (j/lean-name-data (j/request-value identity "name")))))
      (finally (j/close! ctx engine)))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-graph-checks)))
