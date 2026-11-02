(ns java-ir-import-sharing-checks
  "Opt-in target MT reconstruction; source RC is not historical MT evidence."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-header-checks :as header]
            [java-ir-host-checks :as host] [java-ir-generation-checks :as g]
            [java-ir-graph-checks :as graph] [java-ir-logical-sharing-checks :as sharing]
            [java-ir-ref-checks :as ref] [java-ir-array-checks :as array]
            [java-ir-byte-array-checks :as bytes] [java-ir-pointer-checks :as pointer]))
(def ^:dynamic *basis* nil)
(defn setup []
  (let [base (binding [sharing/*basis* *basis*] (sharing/context))
        source (j/source-binding base (Object.))
        row (c/decl "sharing-import-capture" [(c/p 1 "object") (c/p 2 "object")] "object"
              ["dec" {:idx 2} 1 false false (c/ret 1)])
        target (header/header source row) global (header/header source (graph/global-row "sharing-import-global"))
        ctx (j/register-headers base [target global])
        ctx (j/materialize-body ctx target (first (x/raw [row])) [])]
    {:ctx ctx :source source :target target :global global :token (Object.)}))
(defn r [ctx id] (j/graph-ref ctx id))
(defn node [ctx spec] (j/graph-node ctx spec))
(defn recipe [{:keys [ctx source token]} nodes globals values roots]
  (j/selected-owner-ref-payload-mt-graph ctx source token nodes globals values roots))
(defn payload [ctx cell] (aget ^objects (sharing/fields ctx cell) 0))
(defn signature [e]
  [(sharing/counters e) (vec (host/private-value e "constantReady"))
   (host/private-value e "preparedGlobalSources") (host/private-value e "graphInstalled")])
(defn kind-state [ctx value] (sharing/private-call ctx nil "kindMetadata" [(:node-class ctx)] [value]))

(deftest old-profiles-remain-unmarked-while-explicit-profile-reconstructs-sharing
  (doseq [profile [:default :selected :ref-payload]]
    (let [{:keys [ctx source] :as lab} (setup) e (j/machine ctx)
          positive? (not= profile :default)
          nodes [(node ctx {:kind :ref :id 1 :fields [(r ctx 2)]})
                 (node ctx {:kind :ctor :id 2 :rc (if positive? 999 0) :tag 0 :fields [42]})]
          graph (case profile
                  :default (j/prepared-graph ctx source (Object.) nodes [] [] [(r ctx 1)])
                  :selected (j/selected-owner-graph ctx source (Object.) nodes [] [] [(r ctx 1)])
                  :ref-payload (recipe lab nodes [] [] [(r ctx 1)]))
          [cell] (j/install-graph! ctx e graph) value (payload ctx cell)]
      (is (= 0 (c/rc ctx cell))) (is (= (if positive? 1 0) (c/rc ctx value)))
      (is (= (= profile :ref-payload) (sharing/mt? ctx value)))
      (is (false? (sharing/mt? ctx cell)))
      (is (= [2 0 0 0 0] (sharing/counters e)))
      (ref/ref-set! ctx e cell 0) (j/close! ctx e))))

(deftest positive-boundary-failures-are-atomic-even-when-ref-coverage-also-exists
  (let [{:keys [ctx target global] :as lab} (setup) e (j/machine ctx)
        leaf {:kind :ctor :id 2 :rc 100 :tag 0 :fields [42]}
        cell {:kind :ref :id 1 :fields [(r ctx 2)]}
        failures [
          [[cell {:kind :ref :id 2 :rc 100 :fields [0]}] [] [] [(r ctx 1)] #"every Ref to be persistent"]
          [[cell leaf] [global] [(r ctx 2)] [(r ctx 1)] #"positive cache roots"]
          [[cell leaf] [] [] [(r ctx 1) (r ctx 2)] #"positive output roots"]
          [[cell leaf {:kind :ctor :id 3 :tag 0 :fields [(r ctx 2)]}] [] [] [(r ctx 1) (r ctx 3)] #"Only persistent Ref"]
          [[cell leaf {:kind :array :id 3 :fields [(r ctx 2)]}] [] [] [(r ctx 1) (r ctx 3)] #"Only persistent Ref"]
          [[cell leaf {:kind :closure :id 3 :target target :fields [(r ctx 2)]}] [] [] [(r ctx 1) (r ctx 3)] #"Only persistent Ref"]
          [[cell leaf {:kind :ctor :id 3 :rc 100 :tag 0 :fields [(r ctx 3)]}] [] [] [(r ctx 1)] #"Unreachable object"]]]
    (doseq [[specs globals values roots expected] failures]
      (let [before (signature e) graph (recipe lab (mapv #(node ctx %) specs) globals values roots)]
        (is (re-find expected (c/failure #(j/install-graph! ctx e graph))))
        (is (= before (signature e))) (is (= "idle" (j/phase ctx e)))))
    ;; Earlier failures neither consumed the one-install marker nor published a cache slot.
    (is (= [7] (j/install-graph! ctx e (recipe lab [] [] [] [7])))) (j/close! ctx e)))

(deftest exact-positive-region-preserves-duplicate-owner-credits-and-source-association
  (let [{:keys [ctx target global source token] :as lab} (setup) e (j/machine ctx)
        specs [{:kind :ref :id 1 :fields [(r ctx 3)]}
               {:kind :ref :id 2 :fields [(r ctx 3)]}
               {:kind :array :id 3 :rc 999 :fields [(r ctx 4) (r ctx 4) (r ctx 5) (r ctx 6) (r ctx 7)]}
               {:kind :ctor :id 4 :rc 888 :tag 0 :fields [42]}
               {:kind :closure :id 5 :rc 777 :target target :fields [(r ctx 4)]}
               {:kind :byte-array :id 6 :rc 666 :bytes [1 128 255]}
               {:kind :ctor :id 7 :tag 0 :fields [17]}]
        [a b] (j/install-graph! ctx e (recipe lab (mapv #(node ctx %) specs) [global] [(r ctx 1)] [(r ctx 1) (r ctx 2)]))
        array (payload ctx a) [leaf duplicate closure byte-array persistent] (array/elements ctx array)]
    (is (identical? array (payload ctx b))) (is (identical? leaf duplicate))
    (is (identical? leaf (payload ctx closure)))
    (is (= [2 3 1 1] (mapv #(c/rc ctx %) [array leaf closure byte-array])))
    (is (every? #(sharing/mt? ctx %) [array leaf closure byte-array]))
    (is (every? #(not (sharing/mt? ctx %)) [a b persistent]))
    (is (= [1 128 255] (bytes/payload ctx byte-array)))
    (is (identical? a (j/call ctx e "sharing-import-global" [])))
    (let [entries (vals (host/private-value e "preparedGlobalSources")) entry (first entries)]
      (is (= 1 (count entries))) (is (identical? source (host/private-value entry "binding")))
      (is (identical? token (host/private-value entry "acceptedStateToken"))))
    (ref/ref-set! ctx e a 0) (is (= 1 (c/rc ctx array)))
    (ref/ref-set! ctx e b 0)
    (is (every? sharing/dead? [array leaf closure byte-array])) (is (= 0 (c/rc ctx persistent)))
    (j/close! ctx e)))

(deftest taken-rc-one-array-remains-mt-and-native-push-copies-to-fresh-st-storage
  (let [{:keys [ctx] :as lab} (setup) parent (j/machine ctx)
        [cell] (j/install-graph! ctx parent (recipe lab
                 [(node ctx {:kind :ref :id 1 :fields [(r ctx 2)]})
                  (node ctx {:kind :array :id 2 :rc 999 :fields [10]})] [] [] [(r ctx 1)]))
        original (ref/ref-take! ctx parent cell)]
    (is (= 1 (c/rc ctx original))) (is (sharing/mt? ctx original)) (is (not (sharing/exclusive? ctx original)))
    (is (nil? (payload ctx cell))) (pointer/same ctx parent original original)
    (let [word (pointer/word original) {:keys [engine roots]} (j/fork! ctx parent [cell original])
          child engine [child-cell copied] roots]
      (is (sharing/mt? ctx copied)) (is (= word (pointer/word copied)))
      (is (not (identical? (kind-state ctx original) (kind-state ctx copied))))
      (is (= 1 (array/size original) (array/size copied)))
      (let [a (array/push! ctx parent original 20) b (array/push! ctx child copied 30)]
        (is (not (identical? a original))) (is (not (identical? b copied)))
        (is (every? sharing/dead? [original copied]))
        (is (= [10 20] (array/elements ctx a))) (is (= [10 30] (array/elements ctx b)))
        (is (every? #(not (sharing/mt? ctx %)) [a b]))
        (is (every? #(sharing/exclusive? ctx %) [a b]))
        ;; Publishing fresh ST storage through the imported persistent Ref marks it again.
        (ref/ref-set! ctx parent cell a) (ref/ref-set! ctx child child-cell b)
        (is (every? #(sharing/mt? ctx %) [a b]))
        (ref/ref-set! ctx parent cell 0) (ref/ref-set! ctx child child-cell 0)
        (is (every? sharing/dead? [a b])))
      (j/close! ctx parent) (j/close! ctx child))))

(deftest byte-array-and-closure-kind-metadata-survive-sharing-reconstruction-and-fork
  (let [{:keys [ctx target] :as lab} (setup) parent (j/machine ctx)
        [byte-cell closure-cell] (j/install-graph! ctx parent (recipe lab
          [(node ctx {:kind :ref :id 1 :fields [(r ctx 3)]})
           (node ctx {:kind :ref :id 2 :fields [(r ctx 4)]})
           (node ctx {:kind :byte-array :id 3 :rc 999 :bytes [128 255]})
           (node ctx {:kind :closure :id 4 :rc 999 :target target :fields [(r ctx 5)]})
           (node ctx {:kind :ctor :id 5 :rc 999 :tag 0 :fields [42]})] [] [] [(r ctx 1) (r ctx 2)]))
        byte-array (ref/ref-take! ctx parent byte-cell) closure (ref/ref-take! ctx parent closure-cell)]
    (is (= 1 (c/rc ctx byte-array) (c/rc ctx closure)))
    (pointer/same ctx parent byte-array byte-array) (pointer/same ctx parent closure closure)
    (let [{:keys [engine roots]} (j/fork! ctx parent [byte-array closure]) child engine [cb cc] roots]
      (is (every? #(sharing/mt? ctx %) [byte-array closure cb cc]))
      (is (= (pointer/word byte-array) (pointer/word cb))) (is (= (pointer/word closure) (pointer/word cc)))
      (is (not (identical? (kind-state ctx byte-array) (kind-state ctx cb))))
      (is (identical? (kind-state ctx closure) (kind-state ctx cc))) ; immutable Generation
      (doseq [[e b p value] [[parent byte-array closure 1] [child cb cc 2]]]
        (let [fresh (bytes/push! ctx e b value) leaf (j/call ctx e "apply" [p 0])]
          (is (sharing/dead? b)) (is (sharing/dead? p))
          (is (= [128 255 value] (bytes/payload ctx fresh))) (is (not (sharing/mt? ctx fresh)))
          (is (= 1 (c/rc ctx leaf))) (is (sharing/mt? ctx leaf)) (is (not (sharing/exclusive? ctx leaf)))
          (j/release! ctx e fresh) (j/release! ctx e leaf))
        (j/close! ctx e)))))

(deftest persistent-boundaries-stop-marking-and-positive-cycles-keep-native-rc-credits
  (let [{:keys [ctx] :as lab} (setup) parent (j/machine ctx)
        [cell] (j/install-graph! ctx parent (recipe lab
                 [(node ctx {:kind :ref :id 1 :fields [(r ctx 2)]})
                  (node ctx {:kind :ctor :id 2 :rc 999 :tag 0 :fields [(r ctx 2) (r ctx 3)]})
                  (node ctx {:kind :array :id 3 :fields [42]})] [] [] [(r ctx 1)]))
        cycle (payload ctx cell) persistent (aget ^objects (sharing/fields ctx cycle) 1)
        {:keys [engine roots]} (j/fork! ctx parent [cell cycle]) child engine [cc cp] roots]
    (is (= 2 (c/rc ctx cycle) (c/rc ctx cp)))
    (is (identical? cycle (payload ctx cycle))) (is (identical? cp (payload ctx cp)))
    (is (sharing/mt? ctx cycle)) (is (sharing/mt? ctx cp)) (is (not (sharing/mt? ctx persistent)))
    (ref/ref-set! ctx parent cell 0) (ref/ref-set! ctx child cc 0)
    ;; The remaining self-edge owns one credit. No cycle collection is claimed.
    (is (= 1 (c/rc ctx cycle) (c/rc ctx cp))) (is (not (sharing/dead? cycle)))
    (j/close! ctx parent) (j/close! ctx child)))

(deftest deep-positive-payloads-mark-without-java-recursion-or-source-count-copying
  (let [{:keys [ctx] :as lab} (setup) e (j/machine ctx) n 4096
        specs (into [{:kind :ref :id 0 :fields [(r ctx 1)]}]
                    (for [i (range 1 (inc n))]
                      {:kind :ctor :id i :rc 999 :tag 0 :fields [(if (= i n) 0 (r ctx (inc i)))]}))
        [cell] (j/install-graph! ctx e (recipe lab (mapv #(node ctx %) specs) [] [] [(r ctx 0)]))
        values (loop [i n value (payload ctx cell) out []]
                 (if (zero? i) out (recur (dec i) (payload ctx value) (conj out value))))]
    (is (= n (count values))) (is (every? #(= 1 (c/rc ctx %)) values))
    (is (every? #(sharing/mt? ctx %) values))
    (ref/ref-set! ctx e cell 0) (is (every? sharing/dead? values)) (j/close! ctx e)))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-import-sharing-checks)))
