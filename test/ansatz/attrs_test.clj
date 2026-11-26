(ns ansatz.attrs-test
  "Inheriting Lean's @[simp]/@[csimp]/@[extern] attributes (dumped by scripts/dump_attrs.lean as
   NDJSON, bundled as resources/ansatz/init-attrs.ndjson.gz) into Env extensions. load-init!
   auto-imports them, so the inherited set is ON BY DEFAULT (intersected with the store)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [clojure.java.io :as io]
            [ansatz.core :as a]
            [ansatz.codegen :as cg]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as expr]
            [ansatz.kernel.name :as name]
            [ansatz.state :as state]
            [ansatz.attrs :as attrs]))

(use-fixtures :once (fn [f] (a/load-init!) (binding [a/*verbose* false] (f))))

(deftest structured-attribute-json-preserves-escaping-and-legacy-priority
  (let [escaped "Escaped.\"quote\\slashλ"
        lines ["{ \"name\": \"Escaped.\\\"quote\\\\slash\\u03bb\", \"kind\": \"simp\", \"post\": true, \"inv\": false }"
               "{\"kind\":\"csimp\",\"name\":\"Source\\u03bb\",\"target\":\"Target\\\"quoted\"}"
               "{\"kind\":\"simp\",\"name\":\"Explicit\",\"prio\":4294967295}"]
        tuples (attrs/parse-attr-lines lines)
        [loaded _] (attrs/import-attr-tuples (a/env) tuples {:present? (constantly true)})]
    (is (= [["simp" escaped nil nil]
            ["csimp" "Sourceλ" "Target\"quoted" nil]
            ["simp" "Explicit" nil 4294967295]] tuples))
    (is (contains? (env/get-extension loaded :simp-lemmas #{}) escaped))
    (is (= "Target\"quoted" (get (env/get-extension loaded :csimp {}) "Sourceλ")))
    (is (= 4294967295 (get (env/get-extension loaded :simp-priorities {}) "Explicit")))))

(deftest unsupported-and-malformed-attributes-never-mutate-or-probe-presence
  (let [before (a/env)
        valid "{\"kind\":\"extern\",\"name\":\"WouldBeInstalled\"}"
        bad ["{\"kind\":\"unknown\",\"name\":\"Absent\"}"
             "{\"kind\":\"simp\",\"name\":\"Absent\",\"name\":\"Duplicate\"}"
             "{\"kind\":\"simp\",\"name\":\"Absent\",\"extra\":true}"
             "{\"kind\":\"simp\",\"name\":\"Absent\",\"prio\":-1}"
             "{\"kind\":\"simp\",\"name\":\"Absent\",\"prio\":4294967296}"
             "{\"kind\":\"simp\",\"name\":\"Absent\",\"post\":true}"
             "{\"kind\":\"csimp\",\"name\":\"Absent\"}"
             "{\"kind\":\"simp\",\"name\":\"Absent\"} trailing"
             "not json" ""]]
    (doseq [line bad]
      (let [global (atom before) probes (atom 0)]
        (with-redefs [state/ansatz-env global]
          (is (thrown? Exception
                       (attrs/import-attrs! [valid line]
                                            {:present? (fn [_] (swap! probes inc) true)})))
          (is (identical? before @global))
          (is (zero? @probes)))))))

(deftest persisted-tuples-are-validated-as-a-complete-batch
  (doseq [bad [["unknown" "x" nil nil] ["unfold-thms" "x" nil nil]
               ["csimp" "x" nil nil] ["simp" "x" nil -1]
               ["simp" "x" nil nil :ignored]
               ;; a 5th element only on simp, only exactly {:post :inv}, never the default origin
               ["simp" "x" nil nil {:post true :inv false}]
               ["simp" "x" nil nil {:post false}]
               ["simp" "x" nil nil {:post false :inv "true"}]
               ["simp" "x" nil nil {:post false :inv false :prio 1}]
               ["extern" "x" nil nil {:post false :inv false}]]]
    (let [before (a/env) global (atom before)]
      (with-redefs [state/ansatz-env global]
        (is (thrown? clojure.lang.ExceptionInfo
                     (attrs/install-tuples! [["extern" "WouldBeInstalled" nil nil] bad])))
        (is (identical? before @global))))))

(deftest load-init-auto-inherits-lean-attributes
  ;; load-init! ran attrs/load-bundled-attrs!, so the env carries Lean's @[simp] corpus (intersected
  ;; with the bundled Init — a few hundred lemmas), not just the hand-curated core.
  (let [simp-set (env/get-extension (a/env) :simp-lemmas #{})]
    (is (contains? simp-set "Nat.add_zero") "a core @[simp] lemma is inherited")
    (is (contains? simp-set "Option.some.injEq") "and one NOT in the hand-curated default set")
    (is (> (count simp-set) 100) "the inherited set is the real Lean corpus, not the ~40 hand-curated")))

(deftest import-attrs-routing-and-purity
  ;; import-attrs is a PURE env→env function: present names land in the right extension (csimp/impl
  ;; as {from→to} maps, others as sets), absent names skip, and the base env is left untouched.
  (let [lines ["{\"kind\":\"simp\",\"name\":\"Nat.add_zero\"}"          ; present
               "{\"kind\":\"simp\",\"name\":\"Totally.Bogus.Absent\"}"  ; absent → skipped
               "{\"kind\":\"csimp\",\"name\":\"Nat.succ\",\"target\":\"Nat.add\"}" ; map kind: f→g
               "{\"kind\":\"extern\",\"name\":\"Nat.add\"}"]            ; set kind
        e0      (a/env)
        before  (count (env/get-extension e0 :simp-lemmas #{}))
        [e' stats] (attrs/import-attrs e0 lines)]
    (is (contains? (env/get-extension e' :simp-lemmas #{}) "Nat.add_zero") "present simp lemma lands")
    (is (= "Nat.add" (get (env/get-extension e' :csimp {}) "Nat.succ")) "csimp is a {from→to} map")
    (is (contains? (env/get-extension e' :extern #{}) "Nat.add") "extern is a name set")
    (is (pos? (:skipped stats)) "absent name skipped (graceful version-drift handling)")
    (is (= before (count (env/get-extension e0 :simp-lemmas #{})))
        "the base env is unchanged — import-attrs is pure; extensions branch with the immutable env")))

(deftest inherited-simp-set-is-on-by-default
  ;; Option.some.injEq : (some a = some b) = (a = b) is @[simp] in Lean but NOT hand-curated.
  ;; With the inherited set auto-loaded, (simp) closes the goal with NO explicit import — Lean's
  ;; @[simp] set is the default simp set. (Free a,b, so it's unreachable by the hand-curated core.)
  (binding [a/*verbose* false]
    (a/prove-theorem 'opt-inj-default '[a :- Nat, b :- Nat]
                     '(= Prop (= (Option Nat) (Option.some a) (Option.some b)) (= Nat a b)) '[(simp)])
    (is (some? (env/lookup (a/env) (name/from-string "opt-inj-default")))
        "(simp) closed it using the auto-inherited Option.some.injEq — Lean's @[simp] set is on by default")))

(deftest unhandled-extern-lowers-to-clear-throw
  ;; The inherited :extern set (Lean's @[extern] native primitives) lets codegen distinguish a
  ;; native primitive it can't run from an ordinary symbol. The common ones have builtins; the rest
  ;; lower to an explanatory throw instead of a bare symbol → opaque ClassNotFoundException at eval.
  (let [e       (a/env)
        externs (env/get-extension e :extern #{})
        lower   (fn [nm] (cg/ansatz->clj e (expr/const' (name/from-string nm) []) []))
        throw?  (fn [form] (and (seq? form) (= 'throw (first form))))]
    (is (seq externs) "the inherited @[extern] set is populated")
    (is (= 5 ((eval (lower "Nat.add")) 2 3))
        "an extern WITH a builtin still executes its builtin (builtin wins)")
    (is (pos? (count (filter #(throw? (lower %)) externs)))
        "an @[extern] primitive with NO ansatz runtime lowers to an explanatory throw, not a bare symbol")))

(deftest attr-corpus-file-to-tuples-to-env
  ;; A store's attrs corpus (scripts/dump_attrs.lean output) is read ONCE by the importer into
  ;; `[kind name target prio]` tuples, filtered to the store's names, and persisted; a session
  ;; installs the tuples with no presence probe. Simulate with a tiny gzipped corpus.
  (let [dir (doto (java.io.File/createTempFile "ansatz-attrs" "") .delete .mkdirs)
        gz (java.io.File. dir "attrs.ndjson.gz")]
    (with-open [w (java.io.OutputStreamWriter. (java.util.zip.GZIPOutputStream. (io/output-stream gz)))]
      (.write w "{\"kind\":\"simp\",\"name\":\"Nat.add_zero\"}\n")
      (.write w "{\"kind\":\"simp\",\"name\":\"Bool.false_eq\",\"prio\":100}\n")
      (.write w "{\"kind\":\"csimp\",\"name\":\"Nat.succ\",\"target\":\"Nat.add\"}\n"))
    (let [tuples (attrs/read-attr-file (.getPath gz))]
      (is (= 3 (count tuples)))
      (is (= ["simp" "Bool.false_eq" nil 100] (second tuples)) "priority is carried")
      (let [stats (attrs/install-tuples! tuples)]
        (is (= 2 (:simp-lemmas stats)))
        (is (contains? (env/get-extension (a/env) :simp-lemmas #{}) "Nat.add_zero"))
        (is (= 100 (get (env/get-extension (a/env) :simp-priorities {}) "Bool.false_eq")))
        (is (= "Nat.add" (get (env/get-extension (a/env) :csimp {}) "Nat.succ")))))
    (is (nil? (attrs/read-attr-file (str (.getPath dir) "-nope/attrs.ndjson.gz")))
        "a missing corpus reads as nil")))

(deftest inherited-numeric-instances-retain-their-implementations
  ;; The real imported generic instances eta-wrap homogeneous class projections.
  ;; Resolving only the outer H*.mk field leaves named dictionaries in the body.
  (let [c #(expr/const' (name/from-string %) [])
        lit #(expr/lit-nat (biginteger %))
        int-div (expr/app* (c "instHDiv") (c "Int") (c "Int.instDiv"))
        nat-pow (expr/app* (c "instHPow") (c "Nat") (c "Nat")
                           (expr/app* (c "instPowNat") (c "Nat") (c "instNatPowNat")))
        div (expr/app* (c "HDiv.hDiv") (c "Int") (c "Int") (c "Int") int-div
                       (expr/app (c "Int.neg") (lit 5)) (lit 2))
        pow (expr/app* (c "HPow.hPow") (c "Nat") (c "Nat") (c "Nat") nat-pow (lit 3) (lit 34))]
    (is (= -3 (eval (cg/ansatz->clj (a/env) div []))))
    (is (= 16677181699666569N (eval (cg/ansatz->clj (a/env) pow []))))))

(deftest equation-unfold-registrations-preserve-owner-and-order
  ;; SimpTheorems.registerDeclToUnfoldThms records the map independently of
  ;; the per-equation simp registrations made by addDeclToUnfold.
  (let [rows ["{\"kind\":\"unfold-thms\",\"name\":\"f\",\"theorems\":[\"f.eq_2\",\"f.eq_1\"]}"
              "{\"kind\":\"simp\",\"name\":\"f.eq_1\",\"prio\":47,\"post\":true,\"inv\":false}"]
        [loaded stats] (attrs/import-attrs (a/env) rows {:present? (constantly true)})]
    (is (= ["f.eq_2" "f.eq_1"] (get (env/get-extension loaded :simp-unfold-thms {}) "f")))
    (is (= 1 (:simp-unfold-thms stats)))
    (is (contains? (env/get-extension loaded :simp-lemmas #{}) "f.eq_1"))
    (is (= 47 (get (env/get-extension loaded :simp-priorities {}) "f.eq_1")))))
(deftest class-attributes-preserve-identity-without-instances
  (let [tuples (attrs/parse-attr-lines ["{\"kind\":\"class\",\"name\":\"ExportedClass\"}"
                                        "{\"kind\":\"class\",\"name\":\"AbsentClass\"}"])
        [loaded stats] (attrs/import-attr-tuples (env/empty-env) tuples
                                                 {:present? #{"ExportedClass"}})]
    (is (= [["class" "ExportedClass" nil nil] ["class" "AbsentClass" nil nil]] tuples))
    (is (= #{"ExportedClass"} (env/get-extension loaded :classes #{})))
    (is (= 1 (:classes stats)))
    (is (= 1 (:skipped stats)))
    (is (empty? (env/get-extension loaded :instances {})))))

(deftest unfolding-metadata-survives-tuple-installation-and-forks
  (let [tuples (attrs/parse-attr-lines
                ["{\"kind\":\"recursive\",\"name\":\"List.foldl\"}"
                 "{\"kind\":\"smart-unfolding\",\"name\":\"List.foldl\"}"])
        [loaded stats] (attrs/import-attr-tuples (env/empty-env) tuples {:present? (constantly true)})
        forked (env/fork loaded)]
    (is (= [["recursive" "List.foldl" nil nil] ["smart-unfolding" "List.foldl" nil nil]] tuples))
    (is (= {:recursive-defs 1 :smart-unfolding-defs 1} stats))
    (is (contains? (env/get-extension forked :recursive-defs #{}) "List.foldl"))
    (is (contains? (env/get-extension forked :smart-unfolding-defs #{}) "List.foldl"))))

;; ── Lean Origin.decl n post inv: pre-phase and inverse rows ────────────────────────────────

(deftest pre-and-inverse-rows-become-five-tuples
  (let [tuples (attrs/parse-attr-lines
                ["{\"inv\":false,\"kind\":\"simp\",\"name\":\"fwd\",\"post\":true,\"prio\":1000}"
                 "{\"inv\":false,\"kind\":\"simp\",\"name\":\"pre\",\"post\":false,\"prio\":10000}"
                 "{\"inv\":true,\"kind\":\"simp\",\"name\":\"inv\",\"post\":true,\"prio\":1000}"
                 "{\"inv\":true,\"kind\":\"simp\",\"name\":\"preinv\",\"post\":false,\"prio\":1000}"])]
    (is (= [["simp" "fwd" nil 1000]
            ["simp" "pre" nil 10000 {:post false :inv false}]
            ["simp" "inv" nil 1000 {:post true :inv true}]
            ["simp" "preinv" nil 1000 {:post false :inv true}]] tuples))
    (is (true? (:simp-origin-fields? (meta tuples))))
    (is (false? (:simp-origin-fields? (meta (attrs/parse-attr-lines ["{\"kind\":\"simp\",\"name\":\"legacy\",\"prio\":1000}"])))))
    (let [[loaded stats] (attrs/import-attr-tuples (env/empty-env) tuples {:present? (constantly true)})]
      (is (= #{"fwd"} (env/get-extension loaded :simp-lemmas #{})))
      (is (= {"pre" #{{:post false :inv false :prio 10000}}
              "inv" #{{:post true :inv true :prio 1000}}
              "preinv" #{{:post false :inv true :prio 1000}}}
             (env/get-extension loaded :simp-origins {})))
      ;; a ↓ high origin's priority stays with that origin
      (is (empty? (env/get-extension loaded :simp-priorities {})))
      (is (= {:simp-lemmas 1 :simp-origins 3} stats)))))

(deftest replay-follows-lean-addSimpTheorem
  ;; SimpTheorems.lean:612-652: addSimpTheorem erases the registered converse in either
  ;; direction, and never un-erases (tests/elab/issue5828.lean)
  (let [replay #(first (attrs/import-attr-tuples (env/empty-env) % {:present? (constantly true)}))
        fwd ["simp" "n" nil 1000] inv ["simp" "n" nil 1000 {:post true :inv true}]
        pre ["simp" "n" nil 1000 {:post false :inv false}]
        ext #(env/get-extension %1 %2 nil)]
    (testing "n, ←n: the inverse erases the forward rule"
      (let [e (replay [fwd inv])]
        (is (not (contains? (ext e :simp-lemmas) "n")))
        (is (= #{["n" false]} (ext e :simp-erased)))
        (is (= {"n" #{{:post true :inv true :prio 1000}}} (ext e :simp-origins)))
        (is (= {"n" #{{:post true :inv false :prio 1000}}} (ext e :simp-masked)))))
    (testing "←n, n: the forward rule erases the inverse"
      (let [e (replay [inv fwd])]
        (is (contains? (ext e :simp-lemmas) "n"))
        (is (= #{["n" true]} (ext e :simp-erased)))
        (is (empty? (ext e :simp-origins)))))
    (testing "n, ←n, n: both directions erased; the last registration stays masked"
      (let [e (replay [fwd inv fwd])]
        (is (not (contains? (ext e :simp-lemmas) "n")))
        (is (empty? (ext e :simp-origins)))
        (is (= #{["n" false] ["n" true]} (ext e :simp-erased)))
        (is (= #{["n" false]} (ext e :simp-erased-registered)))
        (is (attrs/simp-registered? e "n" false))
        (is (not (attrs/simp-registered? e "n" true)))))
    (testing "the forward pre origin is erased too (BEq ignores the phase)"
      (let [e (replay [pre inv])]
        (is (= {"n" #{{:post true :inv true :prio 1000}}} (ext e :simp-origins)))
        (is (= {"n" #{{:post false :inv false :prio 1000}}} (ext e :simp-masked)))))
    (testing "re-registering in the same phase replaces the priority"
      (let [e (replay [["simp" "n" nil 2000 {:post false :inv false}] ["simp" "n" nil 1000 {:post false :inv false}]])]
        (is (= {"n" #{{:post false :inv false :prio 1000}}} (ext e :simp-origins)))))
    (testing "forward-simp-names: exactly what a persistent index keys"
      (is (= #{"a" "c"}
             (attrs/forward-simp-names [["simp" "a" nil 1000] ["simp" "b" nil 1000 {:post false :inv false}]
                                        ["simp" "c" nil 1000] ["simp" "d" nil 1000]
                                        ["simp" "d" nil 1000 {:post true :inv true}] ["csimp" "e" "f" nil]]))))))
