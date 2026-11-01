(ns java-ir-pointer-hash-control-checks
  "Certificate, source-policy and continuation checks for bounded FoldConsts hashing."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.data.json :as json]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-pointer-hash-checks :as p] [java-ir-pointer-checks :as pointer]
            [java-ir-expr-machinery-checks :as expr] [java-ir-generation-checks :as g]
            [java-ir-host-checks :as h] [java-ir-header-checks :as header]
            [java-ir-code-checks :as code]))
(def ^:dynamic *basis* nil)
(def pv h/private-value)
(defn context ([] (context {})) ([options] (binding [p/*basis* *basis*] (p/context options))))
(defn raw-prefix [tail] (c/let-ir 10 "usize" (p/raw "ptrAddrUnsafe" ["erased" (c/v 1)])
                         (c/let-ir 11 "uint64" (p/raw "USize.toUInt64" [(c/v 10)]) tail)))
(defn salted [salt tail] (raw-prefix (c/let-ir 12 "uint64" salt
                                     (c/let-ir 13 "uint64" (p/raw "mixHash" [(c/v 11) (c/v 12)]) tail))))
(defn bad [body] (c/decl "model-bad-pointer-hash" [(c/p 1 "object")] "uint64" body))
(deftest complete-def-use-audit-rejects-raw-converted-salt-and-unreachable-escapes
  (let [word (c/decl "model-word-identity" [(c/p 1 "uint64")] "uint64" (c/ret 1))
        rows [(bad (salted (c/lit 16) (c/ret 13)))
              (bad (raw-prefix (c/let-ir 12 "uint64" (c/lit 11)
                                 (c/let-ir 14 "uint64" (c/lit 0)
                                   (c/let-ir 15 "uint64" (p/raw "UInt64.xor" [(c/v 12) (c/v 14)])
                                     (c/let-ir 13 "uint64" (p/raw "mixHash" [(c/v 11) (c/v 15)]) (c/ret 13)))))))
              (c/decl "model-bad-pointer-hash" [(c/p 1 "object") (c/p 2 "uint64")] "uint64"
                (raw-prefix (c/let-ir 13 "uint64" (p/raw "mixHash" [(c/v 11) (c/v 2)]) (c/ret 13))))
              (bad (raw-prefix (c/let-ir 13 "uint64" (c/lit 0) (c/ret 13))))
              (bad (p/hash-chain (c/let-ir 14 "object" {:box {:ty "usize" :x {:idx 10}}} (c/ret 13))))
              (bad (p/hash-chain (c/let-ir 14 "object" {:box {:ty "uint64" :x {:idx 11}}} (c/ret 13))))
              (bad (p/hash-chain (c/ret 11)))
              (bad (p/hash-chain ["uset" {:idx 1} 0 {:idx 10} (c/ret 13)]))
              (bad (p/hash-chain ["sset" {:idx 1} 1 0 {:idx 11} "uint64" (c/ret 13)]))
              (bad (p/hash-chain (c/let-ir 14 "uint64" (c/fap "model-word-identity" [(c/v 11)]) (c/ret 14))))
              (bad (p/hash-chain ["jdecl" {:idx 40} [] (c/ret 11) (c/ret 13)]))
              (bad (p/hash-chain ["jdecl" {:idx 40} [(c/p 41 "uint64")] (c/ret 41)
                                 ["jmp" {:idx 40} [(c/v 11)]]]))
              (bad ["jdecl" {:idx 40} [(c/p 41 "uint64")]
                    (raw-prefix (c/let-ir 13 "uint64" (p/raw "mixHash" [(c/v 11) (c/v 41)]) (c/ret 13)))
                    (c/let-ir 12 "uint64" (c/lit 11) ["jmp" {:idx 40} [(c/v 12)]])])]]
    (doseq [row rows]
      (let [{:keys [ctx] :as lab} (context {:rows [word row] :defer #{"model-bad-pointer-hash"}})
            before (:program ctx) message (c/failure #(expr/materialize lab "model-bad-pointer-hash"))]
        (is (re-find #"Pointer|pointer" message)) (is (identical? before (:program ctx)))
        (is (nil? (aget ^objects (pv before "preparedBodies") (int (j/function-id ctx "model-bad-pointer-hash")))))))))
(defn change-private-number [n]
  (if (= "anonymous" (first n)) n
    [(if (= "num" (first n)) "str" (first n)) (change-private-number (second n)) (nth n 2)]))
(deftest exact-policy-source-typed-name-abi-and-once-idle-gates
  (let [{:keys [ctx source headers policy] :as lab} (context) e (j/machine ctx)
        hs (mapv headers (p/roles)) entry (first (filter #(= (first p/hashes) (get % "sha256")) (p/originals))) row (get entry "row")
        issue #(j/declaration-header source % (first p/hashes))
        changed-name (change-private-number (get row "name"))
        wrong-rows [(assoc-in row ["ir" "fdecl" "xs" 0 "borrow"] false)
                    (assoc-in row ["ir" "fdecl" "xs" 0 "x" "idx"] 7)
                    (assoc-in row ["ir" "fdecl" "info"] {"unknown" 0})
                    (assoc-in row ["ir" "fdecl" "type"] "uint64")
                    (assoc-in row ["runtime" "role"] "not-ordinary")
                    (-> row (assoc "name" changed-name) (assoc-in ["ir" "fdecl" "f"] changed-name))]]
    (doseq [wrong wrong-rows] (is (g/bad? #(j/pointer-hash-policy ctx (assoc hs 0 (issue wrong))))))
    (let [foreign (j/declaration-header (j/source-binding ctx (Object.)) row (first p/hashes))]
      (is (g/bad? #(j/pointer-hash-policy ctx (assoc hs 0 foreign)))))
    (j/configure-pointer-hashes! ctx e policy) (is (g/bad? #(j/configure-pointer-hashes! ctx e policy)))
    (is (= 0 (j/instructions ctx e))) (j/close! ctx e)
    (is (g/bad? #(j/configure-pointer-hashes! ctx e policy))))
  (let [one (context) two (context) e (j/machine (:ctx two))]
    (is (g/bad? #(j/configure-pointer-hashes! (:ctx two) e (:policy one)))) (j/close! (:ctx two) e)))
(deftest exact-hash-caller-body-site-and-slot-array-are-bound-before-stamping
  (let [{:keys [ctx policy headers]} (context) e (j/machine ctx) _ (j/configure-pointer-hashes! ctx e policy)
        fns (pv (:program ctx) "functions") bodies (pv (:program ctx) "preparedBodies")
        id (int (j/function-id ctx ((p/roles) 0))) other-id (int (j/function-id ctx ((p/roles) 1)))
        pb (aget ^objects bodies id) site (first (pv pb "pointerHashSites")) target (pv site "target")
        caller (aget ^objects fns id) wrong-caller (aget ^objects fns other-id)
        m (.getDeclaredMethod ^Class (:class ctx) "pointerIdentity"
            (into-array Class [(class target) (class (int-array 0)) (class pb) (class site) (class caller)]))]
    (.setAccessible m true)
    (is (identical? caller (pv pb "caller"))) (is (g/bad? #(.add ^java.util.Set (pv pb "pointerHashSites") nil)))
    (is (g/bad? #(.invoke m e (object-array [target (aclone ^ints (pv site "args")) pb site caller]))))
    (is (g/bad? #(.invoke m e (object-array [target (pv site "args") pb site wrong-caller]))))
    (is (= "idle" (j/phase ctx e))) (j/close! ctx e)))
(deftest populated-target-table-fork-preserves-existing-words-and-sibling-new-identities
  (let [{:keys [ctx] :as lab} (context) parent (p/engine lab) a (p/bvar! ctx parent 0)
        table (p/insert! ctx parent (p/seed! ctx parent) a)
        {:keys [engine roots]} (j/fork! ctx parent [table a]) child engine [ct ca] roots]
    (is (= (pointer/word a) (pointer/word ca)))
    (is (= 1 (p/contains! ctx parent table a) (p/contains! ctx child ct ca)))
    (is (g/bad? #(j/retain! ctx child a)))
    (let [b (p/bvar! ctx parent 1) cb (p/bvar! ctx child 1)
          table (p/insert! ctx parent table b) ct (p/insert! ctx child ct cb)]
      (is (not= (pointer/word b) (pointer/word cb)))
      (is (= 2 (p/size ctx table) (p/size ctx ct)))
      (doseq [[e t x y] [[parent table a b] [child ct ca cb]]]
        (is (= 1 (p/contains! ctx e t x) (p/contains! ctx e t y)))
        (doseq [v [t x y]] (j/release! ctx e v)) (j/close! ctx e)))))
(deftest hash-code-resume-rejection-is-preclaim-and-keeps-pending-arguments
  (when (:explicit *basis*)
    (let [label ((p/roles) 0) {:keys [ctx headers] :as lab} (context {:defer #{label}})
          e (j/machine ctx) table (p/seed! ctx e) key (p/bvar! ctx e 0)]
      (j/start! ctx e label [table key])
      (let [request (j/code-request ctx e) ready (expr/materialize lab label) before (mapv #(c/rc ctx %) [table key])]
        (is (identical? (headers label) (.header request)))
        (is (g/bad? #(j/resume-code! ready e request)))
        (is (identical? request (j/code-request ctx e)))
        (is (= before (mapv #(c/rc ctx %) [table key]))) (is (nil? (pointer/metadata key)))
        (j/fail-code! ctx e request (ex-info "No hash admission in this branch" {})))))
  (when-not (:explicit *basis*) (is true "Code suspension is explicit-driver only")))
(deftest in-flight-pointer-and-conversion-words-copy-unchanged-on-fork
  (when (:explicit *basis*)
    (doseq [next-id [6 7]]
      (let [label ((p/roles) 0) {:keys [ctx] :as lab} (context) parent (p/engine lab)
            table (p/seed! ctx parent) key (p/bvar! ctx parent 0)]
        (j/start! ctx parent "model-owned-pointer-contains" [(p/retain ctx parent table) (p/retain ctx parent key)])
        (expr/until! ctx parent #(and (= label (some-> (pv parent "active") (pv "label")))
                                     (= next-id (some-> (pv parent "pc") (pv "a")))))
        (let [bp (pv parent "bp") words (pv parent "numbers") raw (aget ^longs words (+ bp 5))
              {:keys [engine roots]} (j/fork! ctx parent [table key]) child engine [ct ck] roots]
          (is (= raw (pointer/word key) (pointer/word ck)))
          (when (= next-id 7) (is (= raw (aget ^longs words (+ bp 6)))))
          (is (= raw (aget ^longs (pv child "numbers") (+ (pv child "bp") 5))))
          (doseq [[e t k] [[parent table key] [child ct ck]]]
            (is (= 0 (code/finish! ctx e)))
            (doseq [v [t k]] (j/release! ctx e v)) (j/close! ctx e))))))
  (when-not (:explicit *basis*) (is true "In-flight frames are explicit-driver only")))
(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-pointer-hash-control-checks)))
