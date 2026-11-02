(ns java-ir-name-pool-checks
  "Compact Header Name models; no Source/byte authentication authority."
  (:require [clojure.test :refer [deftest is run-tests]] [clojure.java.io :as io]
            [clojure.data.json :as json] [java-ir-baseline :as j]
            [java-ir-baseline-checks :as c] [java-ir-extern-checks :as x]
            [java-ir-generation-checks :as g])
  (:import [java.util ArrayList HashMap List RandomAccess]
           [java.util.concurrent Callable Executors TimeUnit]))
(def ^:dynamic *basis* nil)
(def digest (apply str (repeat 64 "a")))
(defn base [] (j/prepare-host-program *basis* [] []))
(defn n [leaf] ["str" ["str" ["anonymous"] "Shared"] leaf])
(defn raw [name]
  {"kind" "decl" "name" name "ir" {"fdecl" {"f" name "xs" [] "type" "object" "info" {} "body" ["unreachable"]}}})
(defn issue [source row] (j/declaration-header source row digest))
(defn nm [header] (.name header))
(defn declaration [header] (g/field header "declaration"))
(defn evidence [header] (.metadata header))
(defn java-lists [value]
  (cond (sequential? value) (ArrayList. ^java.util.Collection (mapv java-lists value))
        (map? value) (into {} (map (fn [[k v]] [k (java-lists v)])) value)
        :else value))
(defn uoe? [f] (try (f) false (catch UnsupportedOperationException _ true)))

(deftest canonical-prefix-leaf-and-metadata-sharing
  (let [source (j/source-binding (base) (Object.))
        name (n (String. "entry"))
        row (assoc (raw name) "dependencies" [(java-lists name)] "redirect" (java-lists name)
                   "sourceModule" (java-lists name) "runtime" {"role" "initialized" "initializer" (java-lists name)})
        a (issue source row) b (issue source (raw (java-lists name)))
        exact (nm a) d (declaration a) e (evidence a)]
    (is (instance? RandomAccess exact))
    (doseq [v [(nm b) (get d "f") (first (get e "dependencies")) (get e "redirect")
               (get e "sourceModule") (get-in e ["runtime" "initializer"])]]
      (is (identical? exact v)))
    (let [other (nm (issue source (raw (n "other"))))
          repeated-leaf (nm (issue source (raw ["str" ["str" ["anonymous"] "Other"] (String. "entry")])))]
      (is (identical? (.get ^List exact 1) (.get ^List other 1)))
      (is (identical? (.get ^List exact 2) (.get ^List repeated-leaf 2))))))

(deftest java-list-equality-and-hash-are-bidirectional-across-sources
  (let [ctx (base) a (nm (issue (j/source-binding ctx (Object.)) (raw (n "entry"))))
        b (nm (issue (j/source-binding ctx (Object.)) (raw (java-lists (n "entry")))))
        old (java-lists (n "entry"))]
    (is (not (identical? a b)))
    (doseq [[left right] [[a b] [b a] [a old] [old a] [a (n "entry")] [(n "entry") a]]]
      (is (.equals ^Object left right))
      (is (= (.hashCode ^Object left) (.hashCode ^Object right)))
      (is (= :hit (.get (doto (HashMap.) (.put left :hit)) right))))))

(deftest names-preserve-tag-and-numeric-leaf-class
  (let [source (j/source-binding (base) (Object.)) prefix ["anonymous"]
        names (mapv #(nm (issue source (raw %)))
                    [["num" prefix "1"] ["num" prefix (Long/valueOf 1)]
                     ["num" prefix (Integer/valueOf 1)] ["str" prefix "1"]])]
    (doseq [i (range 4) k (range 4)]
      (is (= (= i k) (.equals ^Object (names i) (names k)))))
    (is (= String (class (.get ^List (names 0) 2))))
    (is (= Long (class (.get ^List (names 1) 2))))
    (is (= Integer (class (.get ^List (names 2) 2)))))
  (let [source (j/source-binding (base) (Object.))
        hash-calls (atom 0) signum-calls (atom 0) mutable-hash (atom 17)
        subclass (proxy [java.math.BigInteger] ["7"]
                   (hashCode [] (swap! hash-calls inc) @mutable-hash)
                   (signum [] (swap! signum-calls inc) 1)
                   (toString [] "7"))
        proxy-name (nm (issue source (raw ["num" ["anonymous"] subclass])))
        exact-name (nm (issue source (raw ["num" ["anonymous"] (java.math.BigInteger. "7")])))]
    (is (not= (.getName (class proxy-name)) (.getName (class exact-name))))
    (is (identical? subclass (.get ^List proxy-name 2)))
    (is (zero? @hash-calls)) (is (zero? @signum-calls))
    ;; No source-pool root retains the extensible leaf. Header metadata still
    ;; keeps its old generic-freezer occurrence, preserving accepted input.
    (let [pool (g/field source "names") nodes ^java.util.Map (g/field pool "nodes")]
      (is (every? #(not (identical? subclass (g/field % "leaf"))) (.values nodes))))
    (let [before (.hashCode ^Object proxy-name)]
      (reset! mutable-hash 31)
      (is (not= before (.hashCode ^Object proxy-name))))))

(deftest compact-names-reject-mutation-including-noops-and-views
  (let [name ^List (nm (issue (j/source-binding (base) (Object.)) (raw (n "entry"))))]
    (doseq [f [#(.set name 2 "changed") #(.add name "changed") #(.remove name (int 0))
               #(.remove name (Object.)) #(.clear name) #(.addAll name [])
               #(.removeAll name []) #(.retainAll name name)
               #(.removeIf name (reify java.util.function.Predicate (test [_ _] false)))
               #(.replaceAll name (reify java.util.function.UnaryOperator (apply [_ v] v)))
               #(.sort name nil) #(.clear (.subList name 0 0))
               #(let [it (.listIterator name)] (.next it) (.set it "changed"))
               #(let [it (.iterator name)] (.next it) (.remove it))]]
      (is (uoe? f)))
    (is (.equals name (java-lists (n "entry"))))))

(deftest mutable-input-is-copied-and-generic-metadata-remains-frozen
  (let [source (j/source-binding (base) (Object.)) name ^List (java-lists (n "entry"))
        dep ^List (java-lists (n "dependency")) generic (ArrayList. ["ordinary" "values"])
        row (-> (raw name) (assoc "dependencies" [dep]) (assoc-in ["ir" "fdecl" "info" "generic"] generic))
        h (issue source row)]
    (.set name 2 "changed") (.set ^List (.get name 1) 2 "changed-prefix")
    (.set dep 2 "changed-dependency") (.add generic "changed-generic")
    (is (.equals ^Object (nm h) (java-lists (n "entry"))))
    (is (.equals ^Object (first (get (evidence h) "dependencies")) (java-lists (n "dependency"))))
    (let [frozen ^List (get-in (declaration h) ["info" "generic"])]
      (is (= ["ordinary" "values"] (vec frozen))) (is (uoe? #(.clear frozen))))))

(deftest malformed-name-freeze-behavior-is-not-normalized
  (let [source (j/source-binding (base) (Object.))
        extra ["str" ["anonymous"] "extra" "preserved"]
        h (issue source (raw extra))]
    ;; Existing name rendering ignores the extra component. Freezing must retain
    ;; it, not silently normalize to a compact three-element key.
    (is (.equals ^Object (nm h) (java-lists extra)))
    (is (= 4 (.size ^List (nm h))))
    (is (not (.equals ^Object (nm h) (java-lists ["str" ["anonymous"] "extra"]))))
    (is (c/failure #(issue source (raw ["str" ["anonymous"] {"mutable" "map"}]))))
    (is (c/failure #(issue source (raw ["str" ["anonymous"] nil]))))))

(deftest concurrent-header-issuance-publishes-one-canonical-name
  (let [source (j/source-binding (base) (Object.)) executor (Executors/newFixedThreadPool 4)]
    (try
      (let [jobs (mapv (fn [_] (.submit executor ^Callable (reify Callable
                                  (call [_] (mapv (fn [_] (nm (issue source (raw (java-lists (n "parallel")))))) (range 32)))))) (range 8))
            names (vec (mapcat #(.get ^java.util.concurrent.Future % 10 TimeUnit/SECONDS) jobs))]
        (is (= 256 (count names))) (is (every? #(identical? (first names) %) names)))
      (finally (.shutdownNow executor)))))

(deftest actual-original-cas-header-fixture-preserves-all-metadata
  (let [source (j/source-binding (base) (Object.))
        rows (json/read-str (slurp (io/file "test/fixtures/java-byte-array-empty-runtime/original-rows.json")))]
    (is (= 3 (count rows)))
    (doseq [{:strs [row sha256]} rows]
      (let [a (j/declaration-header source row sha256) b (j/declaration-header source row sha256)
            ir (get row "ir") d (or (get ir "fdecl") (get ir "extern"))]
        (is (identical? source (.source a)))
        (is (= sha256 (.originalSha256 a)))
        (is (.equals ^Object (nm a) (java-lists (get row "name"))))
        (is (identical? (nm a) (nm b)))
        (is (identical? (nm a) (get (declaration a) "f")))
        (is (.equals ^Object (declaration a) (dissoc d "body")))
        (is (.equals ^Object (evidence a) (select-keys row ["runtime" "dependencies" "redirect" "sourceLocal" "sourceModule"])))))))

(deftest ordinary-name-keys-still-link-and-call-in-both-drivers
  (let [ctx0 (base) source (j/source-binding ctx0 (Object.))
        row (first (x/raw [(c/decl "identity" [(c/p 1 "object")] "object" (c/ret 1))]))
        header (issue source row) registered (j/register-headers ctx0 [header])
        ready (j/materialize-body registered header row [])]
    (is (identical? (aget ^objects (g/field (:program registered) "functions") 0)
                    (aget ^objects (g/field (:program ready) "functions") 0)))
    (doseq [explicit? [false true]
            :let [ctx (assoc ready :explicit explicit?) engine (j/machine ctx)]]
      (try (is (= 0 (j/function-id ctx "identity"))) (is (= 42 (j/call ctx engine "identity" [42])))
           (finally (j/close! ctx engine))))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-name-pool-checks)))
