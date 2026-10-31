(ns generated-nat-arithmetic-checks-v3
  "Pure source/shape/domain models, not actual compiler receipt issuance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json]
            [filesystem-nat-source-profile-v2 :as profile]
            [filesystem-nat-file-run-v1 :as file]
            [generated-command-receipt-v1 :as command]))
(def fixture-directory "test/fixtures/generated-nat-arithmetic/")
(defn- line [root binder suffix]
  (str "def " root " (" binder " : Nat) : Nat := " binder suffix "\n"))
(defn- rejects? [f] (try (f) false (catch Exception _ true)))
(defn- original-delta []
  (into {} (for [line (rest (clojure.string/split-lines (slurp (str fixture-directory "original-output.jsonl"))))
                 :let [row (json/read-str line)]]
             [(get row "name") (get-in row ["ir" "fdecl"])])))
(deftest versioned-source-keeps-identity-default-unchanged
  (let [old (str profile/prefix (line "same" "x" ""))
        arithmetic (str profile/prefix (line "step" "x" " + 1"))]
    (is (= "legacy-private-filesystem-nat-identities/2" (:profile (profile/parse-profile old))))
    (is (nil? (:operation (first (:commands (profile/parse-profile old))))))
    (is (rejects? #(profile/parse-profile arithmetic)))
    (is (= :add-one (:operation (first (:commands (profile/parse-arithmetic-profile arithmetic))))))
    (is (= :add-one (:operation (first (:commands (profile/parse-arithmetic-profile
       (str profile/prefix "def step (x : Nat) : Nat := Nat.add x 1\n")))))))
    (is (= :identity (:operation (first (:commands (profile/parse-arithmetic-profile old))))))))
(deftest mixed-command-positions-and-captured-fields
  (let [a (line "same" "x" "") b (line "step" "other" " + 1") text (str profile/prefix a b)
        capture {:text text :path "HostedArithmetic.lean" :module ["HostedArithmetic"]
                 :byte-count (count text) :sha256 (profile/sha256 text)}
        parsed (profile/captured-arithmetic-profile capture) [first second] (:commands parsed)]
    (is (= [:identity :add-one] (mapv :operation (:commands parsed))))
    (is (= (count profile/prefix) (:start first)))
    (is (= (+ (count profile/prefix) (count a)) (:start second)))
    (is (= b (subs text (:start second) (:end second))))
    (is (= (count text) (get-in parsed [:eof :start]) (get-in parsed [:eof :end]))))
  (doseq [bad [" + 2" " + 01" "+1" " * 1" " + 1 + 1" " + 1 -- hi"]]
    (is (rejects? #(profile/parse-arithmetic-profile (str profile/prefix (line "a" "x" bad)))))))
(deftest arithmetic-grammar-retains-bounds-names-and-original-parser-position-rules
  (doseq [text [(str profile/prefix "def a (x : Nat) : Nat := y + 1\n")
                (str profile/prefix (line "def" "x" " + 1"))
                (str profile/prefix (line "a" "_" " + 1"))
                (str profile/prefix (line "a" "x" "") (line "a" "x" " + 1"))
                (str profile/prefix (line "a" "x" " + 1") "initialize foo\n")
                (apply str profile/prefix (map #(line (str "f" %) "x" " + 1") (range 17)))]]
    (is (rejects? #(profile/parse-arithmetic-profile text))))
  (is (= 16 (:command-count (profile/parse-arithmetic-profile
                              (apply str profile/prefix (map #(line (str "f" %) "x" " + 1") (range 16))))))))
(deftest actual-source-produced-arithmetic-shape-and-abi-remain-verbatim
  (let [delta (original-delta) root ["str" ["anonymous"] "hostedStep"] boxed ["str" root "_boxed"]
        add ["str" ["str" ["anonymous"] "Nat"] "add"]]
    (is (nil? (#'command/arithmetic-batch! delta root boxed)))
    (is (rejects? #(#'command/arithmetic-batch!
                     (-> delta (assoc-in [boxed "body" 1] {"idx" 1})
                         (assoc-in [boxed "body" 4 5 1 "var" "id"] {"idx" 1})) root boxed)))
    (is (= #{add} (#'command/static-calls! (get delta root))))
    (doseq [bad [(assoc-in delta [root "xs" 0 "borrow"] false)
                 (assoc-in delta [boxed "xs" 0 "borrow"] true)
                 (assoc-in delta [root "body" 3 "lit" "v" "num" "v"] 2)
                 (assoc-in delta [root "body" 4 3 "fap" "c"] ["str" ["anonymous"] "foreign"])
                 (assoc-in delta [boxed "body"] ["ret" {"var" {"id" {"idx" 1}}}])]]
      (is (rejects? #(#'command/arithmetic-batch! bad root boxed))))
    ;; Offline compiler rows are structural fixtures, never an issued batch.
    (is (rejects? #(command/batch-summary delta)))))
(deftest source-operation-selection-is-explicit-and-root-bound
  (let [description {:profile "legacy-private-filesystem-nat-arithmetic/3" :action :definition
                     :root "step" :operation :add-one}]
    (is (= :add-one (#'command/selected-operation! {:description description} "step")))
    (is (= :identity (#'command/selected-operation! {:description {}} "step")))
    (doseq [bad [(assoc description :root "other") (assoc description :action :eof)
                 (assoc description :operation :multiply) (dissoc description :operation)]]
      (is (rejects? #(#'command/selected-operation! {:description bad} "step"))))))
(deftest exact-nat-result-domain-and-high-boundaries
  (doseq [n [0 1 Long/MAX_VALUE (biginteger "9223372036854775808")
             (biginteger "18446744073709551616") (.shiftLeft java.math.BigInteger/ONE 200)]]
    (let [next (biginteger (inc (bigint n)))]
      (is (= n (#'file/validate-nat-result! nil n n)))
      (is (= next (#'file/validate-nat-result! :add-one n next)))
      (is (rejects? #(#'file/validate-nat-result! :add-one n n)))))
  (doseq [bad [nil -1 (Object.) (object-array [1]) (bigint 1)
               (proxy [java.math.BigInteger] ["1"] (signum [] (throw (AssertionError. "Not called"))))]]
    (is (rejects? #(#'file/validate-nat-result! :identity 1 bad))))
  (is (rejects? #(#'file/validate-nat-result! :unsupported 1 1))))
(deftest frozen-source-description-has-json-text-keys
  (let [description (#'command/frozen-host
                     {:profile "legacy-private-filesystem-nat-arithmetic/3"
                      :operation :add-one :nested {:source "λ"}})]
    (is (= "legacy-private-filesystem-nat-arithmetic/3" (get description "profile")))
    (is (= {"profile" "legacy-private-filesystem-nat-arithmetic/3"
            "operation" "add-one" "nested" {"source" "λ"}}
           (json/read-str (json/write-str description))))
    (is (rejects? #(#'command/frozen-host {:profile 1 "profile" 2})))))
(defn check! [] (run-tests 'generated-nat-arithmetic-checks-v3))
