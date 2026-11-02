(ns java-ir-selected-owner-checks
  "Selected ownership transport: not a new source proof or cycle collector."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]
            [java-ir-generation-checks :as g]
            [java-ir-graph-checks :as graph]
            [java-ir-header-checks :as h]
            [java-ir-host-checks :as host]
            [java-ir-code-checks :as code]
            [java-ir-ref-checks :as ref]))
(def ^:dynamic *basis* nil)
(defn setup []
  (let [result (binding [graph/*basis* *basis*] (graph/setup))]
    (update result :ctx assoc :explicit (boolean (:explicit *basis*)))))
(defn selected [ctx source nodes globals values roots]
  (j/selected-owner-graph ctx source (Object.) nodes globals values roots))

(deftest default-profile-stays-strict-at-every-value-position
  (let [{:keys [ctx source global identity]} (setup) engine (j/machine ctx)
        signed (j/graph-int ctx -1) r (j/graph-ref ctx 1)
        node #(j/graph-node ctx %)]
    (try
      (doseq [[nodes globals values roots]
              [[[(node {:kind :ref :id 1 :rc 1 :fields [0]})] [] [] [r]]
               [[(node {:kind :ref :id 1 :fields [signed]})] [] [] [r]]
               [[(node {:kind :array :id 1 :fields [signed]})] [] [] [r]]
               [[(node {:kind :ctor :id 1 :tag 0 :fields [signed]})] [] [] [r]]
               [[] [global] [signed] []]
               [[] [] [] [signed]]]]
        (is (g/bad? #(j/prepared-graph ctx source (Object.) nodes globals values roots))))
      (is (g/bad? #(j/graph-int ctx 1.5)))
      (is (g/bad? #(j/graph-node ctx {:kind :ref :id 1 :fields [-1]})))
      (is (false? (host/private-value engine "graphInstalled")))
      (is (= [42] (j/install-graph! ctx engine (selected ctx source [] [] [] [42]))))
      (finally (j/close! ctx engine)))))

(deftest selected-counts-use-every-edge-including-persistent-parent-and-output-aliases
  (let [{:keys [ctx source]} (setup) engine (j/machine ctx)
        r #(j/graph-ref ctx %)
        nodes [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0 :fields [0]})
               (j/graph-node ctx {:kind :array :id 2 :fields [(r 1) (r 1)]})]
        [parent a b] (j/install-graph! ctx engine (selected ctx source nodes [] [] [(r 2) (r 1) (r 1)]))]
    (try
      (is (identical? a b))
      (is (= 4 (c/rc ctx a)))
      (is (= 0 (c/rc ctx parent)))
      (is (identical? a (aget ^objects (graph/fields ctx parent) 0)))
      (j/release! ctx engine a) (j/release! ctx engine b)
      (is (= 2 (c/rc ctx a)))
      (finally (j/close! ctx engine)))))

(deftest cache-and-output-owners-are-independent-and-close-releases-cache-credits
  (let [{:keys [ctx source global]} (setup)
        other (h/header source (graph/global-row "other"))
        ctx (j/register-headers ctx [other]) engine (j/machine ctx) r (j/graph-ref ctx 1)
        [a b] (j/install-graph! ctx engine
                (selected ctx source [(j/graph-node ctx {:kind :ctor :id 1 :rc 99 :tag 0 :fields [42]})]
                          [global other] [r r] [r r]))]
    (is (identical? a b))
    (is (= 4 (c/rc ctx a)))
    (j/release! ctx engine a) (j/release! ctx engine b)
    (is (= 2 (c/rc ctx a)))
    (j/close! ctx engine)
    (is (= 0 (c/rc ctx a)))))

(deftest positive-self-cycle-forks-and-can-be-broken-through-original-ref-wrapper
  (let [ctx (binding [ref/*basis* *basis*] (ref/context))
        source (j/source-binding ctx (Object.)) engine (j/machine ctx) r (j/graph-ref ctx 1)
        [cell] (j/install-graph! ctx engine
                 (selected ctx source [(j/graph-node ctx {:kind :ref :id 1 :rc 9 :fields [r]})] [] [] [r]))
        child (j/fork! ctx engine [cell]) child-engine (:engine child) child-cell (first (:roots child))]
    (try
      (is (= 2 (c/rc ctx cell) (c/rc ctx child-cell)))
      (is (identical? cell (aget ^objects (graph/fields ctx cell) 0)))
      (is (identical? child-cell (aget ^objects (graph/fields ctx child-cell) 0)))
      (ref/ref-set! ctx child-engine child-cell 42)
      (is (= 1 (c/rc ctx child-cell)))
      (is (= 2 (c/rc ctx cell)))
      (is (identical? cell (aget ^objects (graph/fields ctx cell) 0)))
      (ref/ref-set! ctx engine cell 0)
      (is (= 1 (c/rc ctx cell)))
      (finally
        (j/release! ctx engine cell) (j/release! ctx child-engine child-cell)
        (j/close! ctx engine) (j/close! ctx child-engine)))))

(deftest positive-closure-captures-survive-code-pause-and-fork-without-extra-credits
  (let [{:keys [ctx source]} (setup)
        row (c/decl "captured" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))
        target (h/header source row)
        ctx (j/register-headers ctx [target])
        ctx (assoc (j/extend-program ctx (x/raw [(second g/common)])) :explicit true)
        engine (j/machine ctx) r #(j/graph-ref ctx %)
        [closure] (j/install-graph! ctx engine
                    (selected ctx source
                      [(j/graph-node ctx {:kind :closure :id 1 :rc 99 :target target :fields [(r 2)]})
                       (j/graph-node ctx {:kind :ctor :id 2 :rc 99 :tag 0 :fields [42]})]
                      [] [] [(r 1)]))
        captured (aget ^objects (graph/fields ctx closure) 0)]
    (try
      (is (= 1 (c/rc ctx closure) (c/rc ctx captured)))
      (j/start! ctx engine "apply" [closure 0])
      (let [request (code/request! ctx engine)
            child (j/fork! ctx engine []) child-engine (:engine child)
            ready (code/materialize ctx target row [])]
        (try
          (is (identical? captured (first (j/request-value request "arguments"))))
          (is (= 1 (c/rc ctx captured)))
          (j/resume-code! ready engine request)
          (j/resume-code! ready child-engine (j/code-request ready child-engine))
          (let [parent-result (code/finish! ready engine)
                child-result (code/finish! ready child-engine)]
            (is (identical? captured parent-result))
            (is (not (identical? captured child-result)))
            (is (= 1 (c/rc ctx parent-result) (c/rc ctx child-result)))
            (j/release! ctx engine parent-result)
            (j/release! ctx child-engine child-result))
          (finally (j/close! ready child-engine))))
      (finally (j/close! ctx engine)))))

(deftest signed-int-carriers-are-exact-and-descriptors-do-not-escape-import
  (let [{:keys [ctx source]} (setup) engine (j/machine ctx)
        values [-1 Long/MIN_VALUE Long/MAX_VALUE (.negate (.shiftLeft java.math.BigInteger/ONE 80)) (.shiftLeft java.math.BigInteger/ONE 80)]
        imported (j/install-graph! ctx engine
                   (selected ctx source [] [] [] (mapv #(j/graph-int ctx %) values)))
        child (j/fork! ctx engine imported)]
    (try
      (is (= values imported (:roots child)))
      (is (= [Long Long Long java.math.BigInteger java.math.BigInteger] (mapv class imported)))
      (finally (j/close! ctx engine) (j/close! ctx (:engine child))))))

(deftest unreachable-selected-nodes-do-not-consume-the-import-boundary
  (let [{:keys [ctx source]} (setup) engine (j/machine ctx)
        node (j/graph-node ctx {:kind :ref :id 1 :rc 1 :fields [0]})]
    (try
      (is (g/bad? #(j/install-graph! ctx engine (selected ctx source [node] [] [] []))))
      (is (false? (host/private-value engine "graphInstalled")))
      (is (= [42] (j/install-graph! ctx engine (selected ctx source [] [] [] [42]))))
      (finally (j/close! ctx engine)))))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-selected-owner-checks)))
