(ns ansatz.kernel.reducibility-hints-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.env :as env] [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level] [ansatz.kernel.name :as name]
            [ansatz.kernel.hints :as hints] [ansatz.export.codec :as codec]
            [ansatz.export.storage :as storage] [ansatz.export.replay :as replay]
            [boring.core :as boring])
  (:import [ansatz.kernel ConstantInfo TypeChecker Env] [ansatz.export.types CIShell]))
(def prop (e/sort' level/zero))
(def type0 (e/sort' (level/succ level/zero)))
(defn definition [label hint] (env/mk-def (name/from-string label) [] type0 prop :hints hint))
(def cases [:opaque :abbrev {:regular 0} {:regular 1} {:regular 2147483647} {:regular 2147483648} {:regular 4294967295}])
(deftest exact-and-legacy-factories
  (doseq [hint cases]
    (let [^ConstantInfo ci (definition "d" hint)]
      (is (= hint (env/get-reducibility-hints ci)))
      (is (= (hints/code hint) (.getHintsCode ci)))
      (when (map? hint) (is (not= ConstantInfo/HINTS_ABBREV (.getHints ci))))))
  (doseq [legacy [-1 0 1 Integer/MAX_VALUE]]
    (let [ci (ConstantInfo/mkDef (name/from-string "old") (object-array []) type0 prop legacy (byte 0) (object-array []))]
      (is (= legacy (.getHints ci)))
      (is (= (hints/wire-code legacy) (.getHintsCode ci)))))
  (doseq [bad [-1 4294967296 0.5 nil]] (is (thrown? Exception (definition "invalid" {:regular bad}))))
  (is (thrown? Exception (ConstantInfo/mkDef (name/from-string "bad") (object-array []) type0 prop -2 (byte 0) (object-array [])))))
(deftest lazy-delta-orders-full-unsigned-heights
  (let [method (.getDeclaredMethod TypeChecker "compareHints" (into-array Class [Long/TYPE Long/TYPE]))
        _ (.setAccessible method true)
        cmp (fn [a b] (.invoke method nil (object-array [(long a) (long b)])))]
    ;; Same ordering as Lean: abbrev first, decreasing regular heights, opaque last.
    (doseq [[a b expected] [[-2 0 -1] [0 -2 1] [0 1 1] [4294967295 0 -1] [4294967295 2147483648 -1] [0 0 0] [-1 0 1]]]
      (is (= expected (cmp a b)))))
  (let [a (definition "a" {:regular 0}) b (definition "b" {:regular 4294967295})
        en (-> (Env.) (env/check-constant a) (env/check-constant b)) tc (TypeChecker. en)]
    (is (.isDefEq tc (e/const' (.name a) []) (e/const' (.name b) [])))
    (is (.isDefEq tc (e/const' (.name a) []) prop))))
(deftest durable-ci-and-shell-codecs
  (let [registry (codec/registry (fn [_] nil))
        rt #(boring/decode (boring/encode % {:registry registry}) {:registry registry})]
    (doseq [hint cases]
      (let [ci (definition "durable" hint) restored ^ConstantInfo (rt ci)
            shell (CIShell. {:tag 1 :name (.name ci) :lps [] :type-id 0 :value-id 1
                             :hints hint :safety :safe :all [(.name ci)]})
            restored-shell (rt shell)
            resolved (storage/resolve-ci-shell restored-shell #(nth [type0 prop] %))]
        (is (= hint (env/get-reducibility-hints restored)))
        (is (= hint (env/get-reducibility-hints resolved)))
        (is (= (.data shell) (.data ^CIShell restored-shell)))))))
(deftest checked-replay-preserves-exact-hints
  (doseq [hint [{:regular 0} {:regular 4294967295}]]
    (let [ci (definition "replayed" hint) [next result] (replay/replay-one (Env.) ci true)]
      (is (= :ok (:status result)))
      (is (= hint (env/get-reducibility-hints (.lookup ^Env next (.name ci))))))))

(deftest legacy-full-ci-parts-keep-their-documented-meaning
  ;; Exact format-1 DEF vectors used signed integer hints, unlike CIShell maps.
  ;; In particular zero means abbrev; a reader cannot infer a lost regular zero.
  (doseq [[wire expected] [[-1 :opaque] [0 :abbrev] [1 {:regular 1}]
                           [2147483647 {:regular 2147483647}]]]
    (let [nm (name/from-string "legacy")
          ci (#'codec/parts->ci [1 nm [] type0 prop wire 0 [nm]])]
      (is (= expected (env/get-reducibility-hints ci))))))
