(ns java-ir-expr-find-checks
  "Active explicit Expr.find callback/state/ownership checks; no image or kernel replacement."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x] [java-ir-host-checks :as h]
            [java-ir-header-checks :as headers] [java-ir-code-checks :as code]
            [java-ir-generation-checks :as g] [java-ir-sync-task-checks :as sync]
            [java-ir-host-guest-checks :as hg] [java-ir-continuation-checks :as k]
            [java-ir-expr-equality-checks :as eq] [lean-compatibility-corpus :as corpus]))
(def ^:dynamic *basis* nil)
(def directory "test/fixtures/java-expr-find-runtime/")
(defn records [] (json/read-str (slurp (str directory "original-rows.json"))))
(defn record [label] (first (filter #(= label (get % "label")) (records))))
(defn actual-name [label] (get-in (record label) ["row" "name"]))
(defn find-fap [args] {:fap {:c (actual-name "Lean.Expr.findImpl?") :ys args}})
(defn fields [ctx value] (.get ^java.lang.reflect.Field (:fields ctx) value))
(defn ctor-row [tag n]
  (c/decl (str "model-expr-" tag) (mapv #(c/p (inc %) "object") (range n)) "object"
    (c/let-ir (inc n) "object" (c/ctor tag (mapv #(c/v (inc %)) (range n)) (if (<= 6 tag 8) 9 8)) (c/ret (inc n)))))
(defn pred-row [label value type]
  (c/decl label [(c/p 1 "object")] type
    ["dec" {:idx 1} 1 false false (c/let-ir 2 type (c/lit value) (c/ret 2))]))
(defn helpers []
  (concat
    (map-indexed ctor-row [1 1 1 1 2 2 3 3 4 1 2 3])
    [(pred-row "model-false" 0 "object") (pred-row "model-true" 1 "object")
     (pred-row "model-raw-u8" 0 "uint8")
     (c/decl "model-captured-root-search" [(c/p 1 "object")] "object"
       (c/let-ir 2 "object" {:proj {:i 0 :x {:idx 1}}}
         (c/let-ir 3 "object" (find-fap [(c/v 1) (c/v 2)]) ["dec" {:idx 1} 1 false false (c/ret 3)])))
     (c/decl "model-literal" [(c/p 1 "object")] "object" (c/let-ir 2 "object" (c/ctor 0 [(c/v 1)] 0) (c/ret 2)))
     (c/decl "model-find-identity" [(c/p 1 "object")] "object" (c/ret 1))]))
(defn direct [row]
  (let [self (get row "name")]
    (vals (into {} (for [x (tree-seq coll? seq (get-in row ["ir" "fdecl" "body"]))
                        :when (map? x) :let [call (or (get x "fap") (get x "pap"))]
                        :when call :let [n (get call "c")] :when (not= n self)] [(json/write-str n) n])))))
(defn context
  ([] (context {}))
  ([{:keys [rows host-specs defer genuine tasks inactive]}]
   (let [extra (concat (helpers) rows)
         originals (concat (records) (when genuine (eq/records))
                           (when tasks (json/read-str (slurp "test/fixtures/java-task-sync-runtime/original-rows.json"))))
         entries (concat originals (for [r (x/raw extra)] {"label" (last (get r "name")) "row" r "sha256" headers/digest}))
         entries (vals (reduce (fn [m r]
                                (let [n (get-in r ["row" "name"]) old (get m n)]
                                  (when old (assert (= (get old "row") (get r "row"))))
                                  (assoc m n r))) {} entries))
         base (j/prepare-host-program *basis* [] []) source (j/source-binding base {:find-fixture (corpus/sha256 (str directory "provenance.json")) :models true})
         hm (into {} (for [r entries] [(get-in r ["row" "name"]) (j/declaration-header source (get r "row") (get r "sha256"))]))
         registered (j/register-headers base (vec (vals hm)) (or host-specs []))
         ctx (reduce (fn [ctx r]
                       (if (and (get-in r ["row" "ir" "fdecl"]) (not (contains? (set defer) (get r "label"))))
                         (j/materialize-body ctx (hm (get-in r ["row" "name"])) (get r "row")
                           (mapv hm (direct (get r "row")))) ctx)) registered entries)
         ctx (if inactive (assoc ctx :explicit (= inactive :explicit)) (sync/active ctx))]
     {:ctx ctx :source source :headers (into {} (map (fn [r] [(get r "label") (hm (get-in r ["row" "name"]))]) entries))
      :rows (into {} (map (fn [r] [(get r "label") (get r "row")]) entries))})))
(defn invoke [ctx e label args] (j/start! ctx e label args) (sync/finish! ctx e))
(defn mk [ctx e tag & args] (invoke ctx e (str "model-expr-" tag) (vec args)))
(defn predicate [ctx e label] (j/make-closure! ctx e label []))
(defn run-find [ctx e p root] (invoke ctx e "Lean.Expr.findImpl?._boxed" [p root]))
(defn find-action [e]
  (loop [a (sync/action e)] (when a (if (some? (h/private-value a "find")) a (recur (h/private-value a "parent"))))))
(defn find-state [e] (some-> (find-action e) (h/private-value "find")))
(defn drive [ctx e handler]
  (loop [left 100000]
    (assert (pos? left) "Bounded find test did not finish")
    (case (j/phase ctx e)
      "complete" (j/take-result! ctx e)
      "host-call" (let [r (j/host-request ctx e)] (handler r) (recur (dec left)))
      "running" (do (j/advance! ctx e 1) (recur (dec left)))
      (throw (ex-info "Unexpected real boundary" {:phase (j/phase ctx e)})))))
(def host-predicate (h/spec "research_find_predicate" ["object"] [true] "object"))
(defn host-lab [] (context {:rows [(h/ext "model-host-predicate" host-predicate)] :host-specs [host-predicate]}))
(defn start-host-find [ctx e root] (let [p (predicate ctx e "model-host-predicate")] (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p root]) p))
(deftest exact-original-abi-owned-wrappers-and-fixed-profile
  (let [p (json/read-str (slurp (str directory "provenance.json"))) d (get-in (record "Lean.Expr.findImpl?") ["row" "ir" "extern"])]
    (is (= 19 (count (records))))
    (is (= (get p "original-rows-sha256") (corpus/sha256 (str directory "original-rows.json"))))
    (is (= [] (get p "initialized-dependencies")))
    (is (= [["object" "object"] [true true] "tobject"]
           [(mapv #(get % "ty") (get d "xs")) (mapv #(get % "borrow") (get d "xs")) (get d "type")]))
    (is (= [false false] (mapv #(get % "borrow") (get-in (record "Lean.Expr.findImpl?._boxed") ["row" "ir" "fdecl" "xs"]))))))
(deftest none-and-some-preserve-exact-found-owner-and-only-some-allocates
  (let [{:keys [ctx]} (context) e (j/machine ctx)]
    (doseq [[label expected] [["model-false" 0] ["model-true" 1] ["model-raw-u8" 0]]]
      (let [root (mk ctx e 0 7) p (predicate ctx e label) before (h/private-value e "allocations")
            answer (run-find ctx e p root)]
        (is (= expected (- (h/private-value e "allocations") before)))
        (is (true? (h/private-value p "dead")))
        (if (zero? expected)
          (do (is (= 0 answer)) (is (true? (h/private-value root "dead"))))
          (do (is (= 1 (.getInt ^java.lang.reflect.Field (:tag ctx) answer)))
              (is (identical? root (aget ^objects (fields ctx answer) 0)))
              (is (= 1 (c/rc ctx root))) (sync/release! ctx e answer)
              (is (true? (h/private-value root "dead")))))
        (is (nil? (find-state e)))))
    (sync/close! ctx e)))
(deftest genuine-original-hasSorry-and-first-class-owned-find-wrapper
  (let [{:keys [ctx]} (context {:genuine true}) e (j/machine ctx)]
    (doseq [[name expected] [["sorryAx" 1] ["ordinary" 0]]]
      (let [n (invoke ctx e "Lean.Name.str._override" [0 name])
            root (invoke ctx e "Lean.Expr.const._override" [n 0])]
        (is (= expected (invoke ctx e "Lean.Expr.hasSorry._boxed" [root])))))
    (let [root (mk ctx e 0 0) p (predicate ctx e "model-true")
          closure (j/make-closure! ctx e "Lean.Expr.findImpl?._boxed" [])
          apply-row (c/decl "model-apply-find" [(c/p 1 "object") (c/p 2 "object") (c/p 3 "object")] "object"
                      (c/let-ir 4 "object" {:ap {:x {:idx 1} :ys [(c/v 2) (c/v 3)]}} (c/ret 4)))
          next (j/extend-program ctx (x/raw [apply-row]))]
      (j/install-program! next e)
      (let [answer (invoke next e "model-apply-find" [closure p root])]
        (is (identical? root (aget ^objects (fields next answer) 0))) (sync/release! next e answer)))
    (sync/close! ctx e)))
(deftest preorder-includes-partial-apps-and-every-expr-child-order
  (let [{:keys [ctx]} (host-lab) e (j/machine ctx)
        bf (mk ctx e 0 11) br (mk ctx e 0 12) fv (mk ctx e 1 0) mv (mk ctx e 2 0)
        sort (mk ctx e 3 0) con (mk ctx e 4 0 0)
        literal (invoke ctx e "model-literal" [17]) lit (mk ctx e 9 literal)
        proj (mk ctx e 11 0 0 bf) md (mk ctx e 10 0 proj)
        forall (mk ctx e 7 0 mv md) app (mk ctx e 5 con sort)
        lam (mk ctx e 6 0 app forall) let-node (mk ctx e 8 0 fv lit lam)
        root (mk ctx e 5 let-node br)
        expected [root let-node fv lit lam app con sort forall mv md proj bf br]
        seen (atom []) p (start-host-find ctx e root)
        answer (drive ctx e (fn [r] (swap! seen conj (first (h/args r))) (j/resume-host! ctx e r 0)))]
    (is (= 0 answer)) (is (= (count expected) (count @seen)))
    (is (every? true? (map identical? expected @seen)))
    (is (every? #(h/private-value % "dead") (conj expected p))) (sync/close! ctx e)))
(deftest first-match-stops-all-later-predicates-and-detaches-borrowed-history
  (let [{:keys [ctx]} (host-lab) e (j/machine ctx) a (mk ctx e 0 1) b (mk ctx e 0 2) root (mk ctx e 5 a b)
        held (atom nil) calls (atom 0) p (start-host-find ctx e root)
        some (drive ctx e (fn [r] (swap! calls inc) (reset! held (find-state e)) (j/resume-host! ctx e r 1)))]
    (is (= 1 @calls)) (is (identical? root (aget ^objects (fields ctx some) 0)))
    (is (= 1 (c/rc ctx root) (c/rc ctx a) (c/rc ctx b)))
    (doseq [key ["predicate" "root" "current" "found" "option" "packet"]] (is (nil? (h/private-value @held key))))
    (is (zero? (.size ^java.util.Map (h/private-value @held "visited"))))
    (is (zero? (.size ^java.util.Deque (h/private-value @held "pending"))))
    (sync/release! ctx e some) (is (every? #(h/private-value % "dead") [root a b p])) (sync/close! ctx e)))
(deftest sharing-cache-exclusions-and-rc-hint-before-callback-inc
  (doseq [tag [0 1 2 3 4 9 10]]
    (let [{:keys [ctx]} (host-lab) e (j/machine ctx)
          child (when (= tag 10) (mk ctx e 0 99))
          leaf (case tag 0 (mk ctx e 0 0) 1 (mk ctx e 1 0) 2 (mk ctx e 2 0) 3 (mk ctx e 3 0)
                 4 (mk ctx e 4 0 0) 9 (mk ctx e 9 (invoke ctx e "model-literal" [0])) 10 (mk ctx e 10 0 child))
          _ (j/retain! ctx e leaf) root (mk ctx e 5 leaf leaf) seen (atom [])
          p (start-host-find ctx e root)
          answer (drive ctx e (fn [r] (let [current (first (h/args r))]
                                       (swap! seen conj current)
                                       (when (identical? current leaf) (is (= 3 (c/rc ctx leaf)))))
                                    (j/resume-host! ctx e r 0)))
          expected (if (contains? #{0 3 4} tag) [root leaf leaf] (if child [root leaf child] [root leaf]))]
      (is (= 0 answer)) (is (every? true? (map identical? expected @seen))) (is (= (count expected) (count @seen)))
      (is (true? (h/private-value p "dead"))) (sync/close! ctx e))))
(defn mark-mt! [ctx e value]
  (let [m (.getDeclaredMethod ^Class (:class ctx) "markLogicalMT" (into-array Class [Object]))]
    (.setAccessible m true) (.invoke m e (object-array [value]))))
(deftest unique-st-and-logical-mt-ignore-cache-while-counted-shared-and-persistent-cache
  (doseq [mode [:st :mt :shared :persistent]]
    (let [{:keys [ctx source]} (host-lab) e (j/machine ctx)
          root (if (= mode :persistent)
                 (first (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                          [(j/graph-node ctx {:kind :ctor :id 1 :tag 1 :fields [0] :scalars (repeat 8 0)})] [] [] [(j/graph-ref ctx 1)])))
                 (mk ctx e 1 0))
          _ (when (= mode :mt) (mark-mt! ctx e root)) _ (when (= mode :shared) (j/retain! ctx e root))
          seen (atom []) p (start-host-find ctx e root)
          answer (drive ctx e (fn [r]
                               (let [state (find-state e)]
                                 (swap! seen conj (c/rc ctx root))
                                 (is (= (if (contains? #{:st :mt} mode) 0 1) (.size ^java.util.Map (h/private-value state "visited"))))
                                 (is (= 1 (c/rc ctx p))))
                               (j/resume-host! ctx e r 0)))]
      (is (= 0 answer)) (is (= [(case mode :st 2 :mt 2 :shared 3 :persistent 0)] @seen))
      (when (= mode :shared) (is (= 1 (c/rc ctx root))) (sync/release! ctx e root))
      (sync/close! ctx e))))
(deftest predicate-capture-can-back-the-only-root-owner-with-no-extra-entry-retain
  (let [spec (h/spec "research_find_capture" ["object" "object"] [true true] "object")
        row (c/decl "model-capture-pred" [(c/p 1 "object") (c/p 2 "object")] "object"
              (c/let-ir 3 "object" (c/fap "model-capture-host" [(c/v 1) (c/v 2)])
                ["dec" {:idx 1} 1 false false ["dec" {:idx 2} 1 false false (c/ret 3)]]))
        {:keys [ctx]} (context {:rows [(h/ext "model-capture-host" spec) row] :host-specs [spec]}) e (j/machine ctx)
        root (mk ctx e 1 0) p (j/make-closure! ctx e "model-capture-pred" [root]) seen (atom [])]
    (j/start! ctx e "model-captured-root-search" [p])
    (let [answer (drive ctx e (fn [r]
                              (is (every? #(identical? root %) (h/args r)))
                              (swap! seen conj (c/rc ctx root))
                              (is (zero? (.size ^java.util.Map (h/private-value (find-state e) "visited"))))
                              (j/resume-host! ctx e r 1)))]
      (is (= [3] @seen)) (is (identical? root (aget ^objects (fields ctx answer) 0)))
      (is (= 1 (c/rc ctx root))) (is (true? (h/private-value p "dead")))
      (sync/release! ctx e answer) (is (true? (h/private-value root "dead"))) (sync/close! ctx e))))
(deftest raw-borrowed-root-pap-import-and-recursive-inactive-entry-reject
  (let [{:keys [ctx source headers]} (context) e (j/machine ctx) root (mk ctx e 0 0) p (predicate ctx e "model-false")
        counts (k/counters ctx e)]
    (is (g/bad? #(j/start! ctx e "Lean.Expr.findImpl?" [p root])))
    (is (= "idle" (j/phase ctx e))) (is (= counts (k/counters ctx e)))
    (is (g/bad? #(j/make-closure! ctx e "Lean.Expr.findImpl?" [])))
    (is (g/bad? #(context {:rows [(c/decl "model-raw-find-pap" [] "object"
                     (c/let-ir 1 "object" {:pap {:c (actual-name "Lean.Expr.findImpl?") :ys []}} (c/ret 1)))]})))
    (is (g/bad? #(j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                    [(j/graph-node ctx {:kind :closure :id 1 :target (headers "Lean.Expr.findImpl?")})]
                    [] [] [(j/graph-ref ctx 1)]))))
    (is (false? (h/private-value e "graphInstalled")))
    (sync/release! ctx e p) (sync/release! ctx e root) (sync/close! ctx e))
  (doseq [mode [:recursive :explicit]]
    (let [{:keys [ctx]} (context {:inactive mode}) e (j/machine ctx)
          root (j/call ctx e "model-expr-0" [0]) p (predicate ctx e "model-false") before (k/counters ctx e)]
      (is (re-find #"active explicit runtime" (c/failure #(j/call ctx e "Lean.Expr.findImpl?._boxed" [p root]))))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx p) (c/rc ctx root))))))
(deftest invalid-host-reply-is-preclaim-and-invalid-bool-remains-owned-in-receiver
  (let [{:keys [ctx]} (host-lab) e (j/machine ctx) root (mk ctx e 0 0) p (start-host-find ctx e root)
        r (h/request! ctx e)]
    (is (= 2 (c/rc ctx root))) (is (g/bad? #(j/resume-host! ctx e r nil)))
    (is (identical? r (j/host-request ctx e))) (is (= 2 (c/rc ctx root)))
    (j/resume-host! ctx e r 0) (is (= 0 (sync/finish! ctx e)))
    (is (true? (h/private-value root "dead"))) (is (true? (h/private-value p "dead"))) (sync/close! ctx e))
  (let [{:keys [ctx]} (host-lab) e (j/machine ctx) root (mk ctx e 0 0) invalid (mk ctx e 0 9)
        p (start-host-find ctx e root) r (h/request! ctx e)]
    (j/resume-host! ctx e r invalid)
    (is (re-find #"canonical boxed Bool" (c/failure #(sync/finish! ctx e))))
    (let [a (find-action e) state (find-state e) slot (h/private-value a "slot") objects (h/private-value e "objects")]
      (is (identical? invalid (aget ^objects objects slot)))
      (is (true? (h/private-value state "receiverOwned")))
      (is (= 1 (c/rc ctx invalid) (c/rc ctx root) (c/rc ctx p)))
      (is (= "failed" (j/phase ctx e)))
      (is (g/bad? #(j/fork! ctx e []))) (is (g/bad? #(j/start-dispose! ctx e))) (is (g/bad? #(j/close! ctx e))))))
(deftest first-and-second-callback-inc-overflow-preserve-known-loan-progress
  (doseq [which [:predicate :current]]
    (let [{:keys [ctx]} (context) e (j/machine ctx) root (mk ctx e 1 0) p (predicate ctx e "model-false")
          value (if (= which :predicate) p root)]
      ;; Forged count-overflow model, not an accepted source owner ledger.
      (.setInt ^java.lang.reflect.Field (:rc ctx) value Integer/MAX_VALUE)
      (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p root])
      (is (g/bad? #(sync/finish! ctx e)))
      (let [state (find-state e)]
        (is (some? state)) (is (false? (h/private-value state "callbackStarted")))
        (is (= (= which :current) (h/private-value state "predicateCredit")))
        (is (false? (h/private-value state "currentCredit")))
        (is (= (if (= which :predicate) Integer/MAX_VALUE 2) (c/rc ctx p)))
        (is (= (if (= which :current) Integer/MAX_VALUE 1) (c/rc ctx root)))
        (is (= "failed" (j/phase ctx e)))))))
(deftest malformed-head-and-callback-shapes-reject-before-any-loan-inc
  (doseq [[label rows] [["model-wrong-arity" [(c/decl "model-wrong-arity" [(c/p 1 "object") (c/p 2 "object")] "object" (c/ret 1))]]
                        ["model-wrong-result" [(c/decl "model-wrong-result" [(c/p 1 "object")] "uint64"
                                               (c/let-ir 2 "uint64" (c/lit 0) (c/ret 2)))]]]]
    (let [{:keys [ctx]} (context {:rows rows}) e (j/machine ctx) root (mk ctx e 0 0) p (predicate ctx e label)
          before (k/counters ctx e)]
      (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p root])
      (is (g/bad? #(sync/finish! ctx e))) (is (= before (k/counters ctx e)))
      (is (= 1 (c/rc ctx p) (c/rc ctx root))) (is (nil? (find-state e)))))
  (let [{:keys [ctx source]} (context) e (j/machine ctx)
        [bad] (j/install-graph! ctx e (j/prepared-graph ctx source (Object.)
                   [(j/graph-node ctx {:kind :ctor :id 1 :tag 0 :fields [0] :scalars (repeat 7 0)})] [] [] [(j/graph-ref ctx 1)]))
        p (predicate ctx e "model-false") before (k/counters ctx e)]
    (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p bad])
    (is (re-find #"storage layout" (c/failure #(sync/finish! ctx e))))
    (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx p))) (is (nil? (find-state e)))))
(deftest callback-code-demand-and-host-fork-never-replay-loan-acquisition
  (let [callback (c/decl "model-code-pred" [(c/p 1 "object")] "object"
                   (c/let-ir 2 "object" (c/fap "model-host-predicate" [(c/v 1)])
                     ["dec" {:idx 1} 1 false false (c/ret 2)]))
        {:keys [ctx headers rows]} (context {:rows [(h/ext "model-host-predicate" host-predicate) callback]
                                            :host-specs [host-predicate] :defer #{"model-code-pred"}})
        parent (j/machine ctx) root (mk ctx parent 0 0) p (predicate ctx parent "model-code-pred")]
    (j/start! ctx parent "Lean.Expr.findImpl?._boxed" [p root])
    (let [request (code/request! ctx parent) state (find-state parent)
          {:keys [engine roots]} (j/fork! ctx parent [root p]) child engine [cr cp] roots
          ready (j/materialize-body ctx (headers "model-code-pred") (rows "model-code-pred") [(headers "model-host-predicate")])]
      (is (identical? (headers "model-code-pred") (.header request)))
      (is (true? (h/private-value state "callbackStarted")))
      (is (false? (h/private-value state "predicateCredit"))) (is (false? (h/private-value state "currentCredit")))
      (is (= 2 (c/rc ctx root) (c/rc ctx cr))) (is (= 1 (c/rc ctx p) (c/rc ctx cp)))
      (is (identical? cr (h/private-value (find-state child) "current")))
      (doseq [[e er answer] [[parent root 0] [child cr 1]]]
        (j/resume-code! ready e (j/code-request ready e))
        (let [r (h/request! ready e)]
          (is (identical? er (first (h/args r)))) (is (= 2 (c/rc ready er)))
          (j/resume-host! ready e r answer)
          (let [result (sync/finish! ready e)]
            (if (zero? answer) (is (= 0 result))
              (do (is (identical? er (aget ^objects (fields ready result) 0))) (sync/release! ready e result)))))
        (is (true? (h/private-value er "dead"))) (sync/close! ready e)))))
(deftest host-fork-copies-nonempty-visited-and-pending-aliases-per-branch
  (let [{:keys [ctx]} (host-lab) parent (j/machine ctx) leaf (mk ctx parent 1 0)
        _ (j/retain! ctx parent leaf) root (mk ctx parent 5 leaf leaf) p (start-host-find ctx parent root)
        first-request (h/request! ctx parent)]
    (is (identical? root (first (h/args first-request))))
    (j/resume-host! ctx parent first-request 0)
    (let [second-request (h/request! ctx parent) state (find-state parent)
          {:keys [engine roots]} (j/fork! ctx parent [root leaf p]) child engine [cr cl cp] roots
          cs (find-state child) pm (h/private-value state "visited") cm (h/private-value cs "visited")]
      (is (identical? leaf (first (h/args second-request)))) (is (= 3 (c/rc ctx leaf) (c/rc ctx cl)))
      (is (not (identical? state cs))) (is (not (identical? pm cm)))
      (is (.containsKey ^java.util.Map pm leaf)) (is (.containsKey ^java.util.Map cm cl))
      (is (not (.containsKey ^java.util.Map cm leaf)))
      (is (identical? cl (.peek ^java.util.Deque (h/private-value cs "pending"))))
      (doseq [[e current answer] [[parent leaf 1] [child cl 0]]]
        (j/resume-host! ctx e (j/host-request ctx e) answer)
        (let [result (sync/finish! ctx e)]
          (if (zero? answer) (is (= 0 result))
            (do (is (identical? current (aget ^objects (fields ctx result) 0)))
                (is (= 1 (c/rc ctx current))) (sync/release! ctx e result))))
        (is (true? (h/private-value current "dead")))
        (is (zero? (.size ^java.util.Map (h/private-value (if (identical? e parent) state cs) "visited"))))
        (sync/close! ctx e)))))
(deftest fork-before-first-visit-and-after-bool-receiver-preserves-stage
  (let [{:keys [ctx]} (context) parent (j/machine ctx) root (mk ctx parent 0 0) p (predicate ctx parent "model-true")]
    (j/start! ctx parent "Lean.Expr.findImpl?._boxed" [p root])
    (loop [left 1000] (assert (pos? left))
      (if (find-state parent) nil (do (j/advance! ctx parent 1) (recur (dec left)))))
    (is (= 0 (h/private-value (find-state parent) "encounters")))
    (let [{:keys [engine roots]} (j/fork! ctx parent [root]) child engine [cr] roots]
      (doseq [[e er] [[parent root] [child cr]]]
        (let [answer (sync/finish! ctx e)] (is (identical? er (aget ^objects (fields ctx answer) 0)))
              (sync/release! ctx e answer)) (sync/close! ctx e))))
  (let [{:keys [ctx]} (host-lab) parent (j/machine ctx) root (mk ctx parent 0 0) _ (start-host-find ctx parent root)
        request (h/request! ctx parent)]
    (j/resume-host! ctx parent request 1)
    (loop [left 1000]
      (assert (pos? left))
      (let [a (find-action parent) slot (h/private-value a "slot") objects (h/private-value parent "objects")]
        (if (= 1 (aget ^objects objects slot)) nil (do (j/advance! ctx parent 1) (recur (dec left))))))
    ;; Slot is already the owner authority before Find observes/validates it.
    (let [{:keys [engine roots]} (j/fork! ctx parent [root]) child engine [cr] roots]
      (doseq [[e er] [[parent root] [child cr]]]
        (let [answer (sync/finish! ctx e)] (is (identical? er (aget ^objects (fields ctx answer) 0)))
              (sync/release! ctx e answer)) (sync/close! ctx e)))))
(deftest nested-find-has-independent-borrowed-maps-and-no-extra-root-credits
  (let [nested (c/decl "model-nested-predicate" [(c/p 1 "object")] "object"
                 (c/let-ir 2 "object" {:pap {:c (c/name-ir "model-host-predicate") :ys []}}
                   (c/let-ir 3 "object" {:fap {:c (actual-name "Lean.Expr.findImpl?._boxed") :ys [(c/v 2) (c/v 1)]}}
                     ["dec" {:idx 3} 1 false false (c/let-ir 4 "object" (c/lit 0) (c/ret 4))])))
        {:keys [ctx]} (context {:rows [(h/ext "model-host-predicate" host-predicate) nested] :host-specs [host-predicate]})
        e (j/machine ctx) root (mk ctx e 1 0) p (predicate ctx e "model-nested-predicate")]
    (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p root])
    (let [r (h/request! ctx e) inner (find-action e) outer (h/private-value inner "parent")
          a (h/private-value inner "find") b (h/private-value outer "find")]
      (is (some? b)) (is (not (identical? a b)))
      (is (identical? root (h/private-value a "current"))) (is (identical? root (h/private-value b "current")))
      (is (= 3 (c/rc ctx root)))
      (is (= 1 (.size ^java.util.Map (h/private-value a "visited"))))
      (is (= 0 (.size ^java.util.Map (h/private-value b "visited"))))
      (j/resume-host! ctx e r 1)
      (is (= 0 (sync/finish! ctx e))) (is (true? (h/private-value root "dead")))
      (is (true? (h/private-value p "dead"))) (sync/close! ctx e))))
(deftest deep-app-chain-and-shared-dag-use-bounded-explicit-control
  (let [{:keys [ctx]} (context) e (j/machine ctx)
        chain (loop [i 0 value (mk ctx e 0 0)]
                (if (= i 4096) value (recur (inc i) (mk ctx e 5 value (mk ctx e 0 i)))))
        p (predicate ctx e "model-false")]
    (is (= 0 (run-find ctx e p chain))) (is (true? (h/private-value chain "dead")))
    (let [dag (loop [i 0 value (mk ctx e 0 0)]
                (if (= i 22) value (do (j/retain! ctx e value) (recur (inc i) (mk ctx e 5 value value)))))
          p (predicate ctx e "model-false") before (h/private-value e "retains")]
      (is (= 0 (run-find ctx e p dag)))
      ;; 22 App identities and TWO BVar occurrences; each callback INCs p/e.
      (is (= 48 (- (h/private-value e "retains") before)))
      (is (true? (h/private-value dag "dead"))))
    (sync/close! ctx e)))
(deftest explicit-work-and-pending-limit-models-preserve-borrowed-state
  (doseq [mode [:work :pending :visited]]
    (let [{:keys [ctx]} (context) e (j/machine ctx)
          root (if (= mode :pending) (mk ctx e 5 (mk ctx e 0 0) (mk ctx e 0 1)) (mk ctx e 1 0))
          _ (when (= mode :visited) (j/retain! ctx e root))
          p (predicate ctx e "model-false")]
      (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p root])
      (loop [left 1000] (assert (pos? left))
        (if (find-state e) nil (do (j/advance! ctx e 1) (recur (dec left)))))
      (let [state (find-state e)]
        ;; Private control-limit models, not source-generated traversal states.
        (case mode
          :work (sync/private-set! state "encounters" (long 1000000))
          :pending (let [q ^java.util.Deque (h/private-value state "pending")]
                     (dotimes [_ 99999] (.push q root)))
          :visited (sync/private-set! state "visited"
                     (proxy [java.util.IdentityHashMap] [] (size [] 100000))))
        (is (re-find #"Expr.find.*bounded runtime profile" (c/failure #(sync/finish! ctx e))))
        (is (= "failed" (j/phase ctx e)))
        (is (= 1 (c/rc ctx p))) (is (= (if (= mode :visited) 2 1) (c/rc ctx root)))
        (is (false? (h/private-value state "predicateCredit")))
        (is (false? (h/private-value state "currentCredit")))))))
(deftest interrupted-next-dispatch-does-not-touch-callback-owner-credits
  (let [{:keys [ctx]} (context) e (j/machine ctx) root (mk ctx e 1 0) p (predicate ctx e "model-false")]
    (j/start! ctx e "Lean.Expr.findImpl?._boxed" [p root])
    (loop [left 1000] (assert (pos? left))
      (if (find-state e) nil (do (j/advance! ctx e 1) (recur (dec left)))))
    (sync/private-set! (find-state e) "encounters" (long 1023))
    (let [before (k/counters ctx e) answer (atom nil)
          worker (Thread. ^Runnable (fn [] (.interrupt (Thread/currentThread))
                                      (try (reset! answer (c/failure #(j/advance! ctx e 1)))
                                           (finally (Thread/interrupted)))))]
      (.start worker) (.join worker 1000)
      (is (not (.isAlive worker))) (is (re-find #"Expr.find interrupted" (or @answer "")))
      (is (= before (k/counters ctx e))) (is (= 1 (c/rc ctx p) (c/rc ctx root))))))
(deftest callback-failure-keeps-loans-and-search-with-no-replay-or-cleanup-claim
  (let [{:keys [ctx]} (host-lab) e (j/machine ctx) root (mk ctx e 1 0) p (start-host-find ctx e root)
        r (h/request! ctx e) state (find-state e)]
    (j/fail-host! ctx e r (ex-info "model callback failure" {}))
    (is (= "failed" (j/phase ctx e))) (is (identical? state (find-state e)))
    (is (true? (h/private-value state "callbackStarted")))
    (is (= 2 (c/rc ctx root))) (is (= 1 (c/rc ctx p)))
    (is (g/bad? #(j/resume-host! ctx e r 0))) (is (g/bad? #(j/fork! ctx e [])))
    (is (g/bad? #(j/start-dispose! ctx e))) (is (g/bad? #(j/close! ctx e)))))
(deftest claimed-host-completion-cleanup-can-demand-code-host-and-fork-inside-find
  (let [consume (h/spec "research_find_consume_promise" ["object"] [true] "object")
        event (h/spec "research_find_finalizer_event" ["object"] [true] "object")
        finalizer (c/decl "model-find-finalizer" [(c/p 1 "object")] "object"
                    (c/let-ir 2 "object" (c/fap "model-find-finalizer-event" [(c/v 1)])
                      ["dec" {:idx 1} 1 false false (c/ret 2)]))
        callback (c/decl "model-find-cleanup-predicate" [(c/p 1 "object")] "object"
                   (c/let-ir 10 "object" (c/lit 1) (c/let-ir 2 "object" (sync/sfap "IO.Promise.new._boxed" ["erased" "erased" "erased"])
                     ["inc" {:idx 2} 1 false false
                      (c/let-ir 3 "object" (sync/sfap "IO.Promise.result?._boxed" ["erased" (c/v 2)])
                        (c/let-ir 4 "object" {:pap {:c (c/name-ir "model-find-finalizer") :ys []}}
                          (c/let-ir 5 "object" (sync/sfap "Task.map._boxed" ["erased" "erased" (c/v 4) (c/v 3) "erased" (c/v 10)])
                            (c/let-ir 6 "object" {:pap {:c (c/name-ir "model-find-consume-promise") :ys []}}
                              (c/let-ir 7 "object" {:ap {:x {:idx 6} :ys [(c/v 2)]}}
                                ["dec" {:idx 5} 1 false false
                                 ["dec" {:idx 1} 1 false false
                                  (c/let-ir 8 "object" (c/lit 0) (c/ret 8))]])))))])))
        {:keys [ctx headers rows]}
        (context {:tasks true :host-specs [consume event] :defer #{"model-find-finalizer"}
                  :rows [(h/ext "model-find-consume-promise" consume)
                         (h/ext "model-find-finalizer-event" event) finalizer callback]})
        parent (j/machine ctx) root (mk ctx parent 1 0) p (predicate ctx parent "model-find-cleanup-predicate")]
    (j/start! ctx parent "Lean.Expr.findImpl?._boxed" [p root])
    (let [r (h/request! ctx parent) promise (first (h/args r))]
      (is (= "research_find_consume_promise" (j/request-value r "symbol")))
      (is (= 1 (c/rc ctx promise))) (is (= 2 (c/rc ctx root)))
      (j/resume-host! ctx parent r 0)
      (let [request (code/request! ctx parent) completion (h/private-value parent "hostCompletion")
            {:keys [engine roots]} (j/fork! ctx parent [root p promise]) child engine [cr cp cpromise] roots
            ready (j/materialize-body ctx (headers "model-find-finalizer") (rows "model-find-finalizer")
                                      [(headers "model-find-finalizer-event")])]
        (is (identical? (headers "model-find-finalizer") (.header request)))
        (is (true? (h/private-value completion "replyClaimed")))
        (is (true? (h/private-value (h/private-value child "hostCompletion") "replyClaimed")))
        (is (some? (find-state parent))) (is (some? (find-state child)))
        (is (= 2 (c/rc ctx root) (c/rc ctx cr)))
        (doseq [[e er ep dead-promise answer] [[parent root p promise 0] [child cr cp cpromise 77]]]
          (j/resume-code! ready e (j/code-request ready e))
          (let [r (h/request! ready e)]
            (is (= "research_find_finalizer_event" (j/request-value r "symbol")))
            (is (= [0] (h/args r)))
            (j/resume-host! ready e r answer))
          (is (= 0 (sync/finish! ready e)))
          (is (every? #(h/private-value % "dead") [er ep dead-promise]))
          (is (nil? (h/private-value e "hostCompletion"))) (is (nil? (find-state e)))
          (is (sync/quiescent? ready e)) (sync/close! ready e))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-expr-find-checks)))
