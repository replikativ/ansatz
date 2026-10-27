(ns ansatz.meta.match.matcher-info-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.matchers :as imported]
            [ansatz.meta.match.matcher-info :as mi]))

(def info
  (mi/matcher-info 2 2 [(mi/alt-param-info 1 0 false) (mi/alt-param-info 0 1 false)]
                   0 [(mi/discr-info "h") (mi/discr-info)] [[0 1]]))

(deftest matcher-argument-ranges-and-alternative-binders
  (is (= (mi/discr-info "h") (mi/discr-info (name/from-string "h"))))
  (is (= 2 (mi/num-alts info)))
  (is (= 7 (mi/arity info)))
  (is (= 2 (mi/get-motive-pos info)))
  (is (= 3 (mi/get-first-discr-pos info)))
  (is (= [3 4] (vec (mi/get-discr-range info))))
  (is (= 5 (mi/get-first-alt-pos info)))
  (is (= [5 6] (vec (mi/get-alt-range info))))
  (is (= 1 (mi/get-num-discr-eqs info)))
  (is (= 1 (mi/get-num-eqs-from-discr-infos [(mi/discr-info) (mi/discr-info "h")])))
  (is (= [2 2] (mi/alt-num-params info)))
  (is (= [1] (mi/alt-num-params (mi/matcher-info 0 1 [(mi/alt-param-info 0 0 true)]
                                               0 [(mi/discr-info)] [])))))

(deftest overlaps-are-directed-idempotent-and-sorted
  (let [o (-> [] (mi/overlaps-insert 3 2) (mi/overlaps-insert 0 2)
              (mi/overlaps-insert 3 2) (mi/overlaps-insert 2 3))]
    (is (= 3 (count o)))
    (is (= [0 3] (mi/overlaps-overlapping o 2)))
    (is (= [2] (mi/overlaps-overlapping o 3)))
    (is (= [] (mi/overlaps-overlapping o 1)))))

(deftest generated-and-imported-info-share-an-immutable-extension
  (let [base (env/empty-env)
        n (name/from-string "Local.match_1")
        out (mi/add-matcher-info base n info)]
    (is (nil? (mi/get-matcher-info-core? base n)))
    (is (= info (imported/matcher-info out (str n))))
    (is (= info (mi/get-matcher-info-core? out n)))
    (is (mi/is-matcher-core out n))
    (is (not (mi/is-matcher-core out (name/from-string "Unknown.match_1"))))
    (is (= (env/get-extension out :matcher-info {})
           (env/get-extension (imported/install base {(str n) info}) :matcher-info {})))
    ;; Lookup remains compatible with role/session metadata whose names are not match_N.
    (is (= info (imported/matcher-info (mi/add-matcher-info base "role.matcher" info)
                                     "role.matcher")))))

(deftest matcher-application-recognition-requires-saturation
  (let [n (name/from-string "Local.match_1")
        out (mi/add-matcher-info (env/empty-env) n info)
        f (e/const' n [])
        args (repeat (mi/arity info) (e/lit-nat 0))
        full (reduce e/app f args)]
    (is (nil? (mi/is-matcher-app-core? out f)))
    (is (nil? (mi/is-matcher-app-core? out (reduce e/app f (rest args)))))
    (is (= info (mi/is-matcher-app-core? out full)))
    (is (= info (mi/is-matcher-app-core? out (e/app full (e/lit-nat 1)))))
    (is (mi/is-matcher-app-core out full))
    (is (not (mi/is-matcher-app-core out (e/app (e/fvar 1) (e/lit-nat 0)))))
    (is (not (mi/is-matcher-app-core (env/empty-env) full)))))

(deftest bundled-metadata-roundtrips-without-a-second-representation
  (let [rows (imported/bundled-matchers)
        out (imported/install (env/empty-env) rows)]
    (is (> (count rows) 2000))
    (doseq [[n expected] rows]
      (let [info (mi/get-matcher-info-core? out (name/from-string n))
            rebuilt (mi/matcher-info (:num-params info) (:num-discrs info) (:alts info)
                                     (:u-elim-pos info) (mapv mi/discr-info (:discrs info))
                                     (:overlaps info))]
        (is (= expected info rebuilt) n)
        (is (= (:num-discrs info) (count (mi/get-discr-range info))))
        (is (= (count (:alts info)) (count (mi/get-alt-range info))))
        (is (= (imported/non-overlapping? info) (mi/non-overlapping? info)))
        (is (every? nat-int? (mi/alt-num-params info)))))))

(deftest splitter-status-includes-overlap-assumptions
  (is (nil? (mi/non-overlapping? nil)))
  (is (not (mi/non-overlapping? info)))
  (is (not (mi/non-overlapping? (assoc info :overlaps []))))
  (is (mi/non-overlapping? (assoc info :overlaps [] :alts [(mi/alt-param-info 0 0 true)]))))
