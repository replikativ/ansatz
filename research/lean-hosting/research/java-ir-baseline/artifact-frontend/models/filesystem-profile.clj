(ns filesystem-nat-source-profile-v2-checks
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as str]
            [filesystem-nat-source-profile-v2 :as p]))
(defn- line [root binder] (str "def " root " (" binder " : Nat) : Nat := " binder "\n"))
(defn- rejects? [text] (try (p/parse-profile text) false (catch clojure.lang.ExceptionInfo _ true)))
(deftest exact-two-definition-spans
  (let [a (line "first" "x") b (line "second" "other") text (str p/prefix a b)
        result (p/parse-profile text) [first-command second-command] (:commands result)
        start (count p/prefix) second-start (+ start (count a)) end (count text)]
    (is (= 2 (:command-count result)))
    (is (= ["first" "second"] (mapv :root (:commands result))))
    (is (= ["x" "other"] (mapv :binder (:commands result))))
    (is (= [start second-start] (mapv :start (:commands result))))
    (is (= [second-start end] (mapv :next-start (:commands result))))
    (is (= [start start] (mapv :previous-start (:commands result))))
    (is (= [0 1] (mapv :baseline-count (:commands result))))
    (is (= [1 2] (mapv :observed-count (:commands result))))
    (is (= :definition (:action first-command)))
    (is (= (subs text (:start second-command) (:end second-command)) b))
    (is (= {:action :eof :index 2 :root nil :binder nil :start end :end end
            :next-start end :previous-start second-start :baseline-count 2 :observed-count 3}
           (:eof result)))))
(deftest third-command-previous-position
  (let [result (p/parse-profile (apply str p/prefix (map #(line % "x") ["a" "b" "c"])))
        [a b c] (:commands result)]
    (is (= (:start b) (:previous-start c)))
    (is (= (:end a) (:start b)))
    (is (= (:end b) (:start c)))
    (is (= 2 (:baseline-count c)))))
(deftest one-and-sixteen-definition-boundaries
  (let [one (p/parse-profile (str p/prefix (line "single" "v")))
        sixteen (p/parse-profile (apply str p/prefix (map #(line (str "f" %) "x") (range 16))))]
    (is (= 1 (:command-count one)))
    (is (= 16 (:command-count sixteen)))
    (is (= (:start (first (:commands one))) (get-in one [:eof :previous-start])))
    (is (rejects? p/prefix))
    (is (rejects? (apply str p/prefix (map #(line (str "f" %) "x") (range 17)))))))
(deftest reject-source-outside-finite-profile
  (doseq [text [(str "import Init.Prelude\n" (line "a" "x"))
                (str "module\n" p/prefix (line "a" "x"))
                (str p/prefix "\n" (line "a" "x"))
                (str p/prefix "-- comment\n" (line "a" "x"))
                (str p/prefix "set_option autoImplicit false\n" (line "a" "x"))
                (str p/prefix "import Other\n" (line "a" "x"))
                (str p/prefix "def a (x : Nat) : Nat := 0\n")
                (str p/prefix "def a (x : Nat) : Nat := y\n")
                (str p/prefix "def a (x : Nat) : Nat := x")
                (str p/prefix (line "a" "x") (line "a" "y"))
                (str p/prefix (line "def" "x"))
                (str p/prefix (line "a" "_"))
                (str p/prefix (line "a.b" "x"))
                (str p/prefix (line "α" "x"))
                (str p/prefix (line "a" "x") "\u0000")
                (str/replace (str p/prefix (line "a" "x")) "\n" "\r\n")
                (str p/prefix (line (apply str (repeat 65 "a")) "x"))
                (apply str (repeat (inc p/max-source-bytes) "a"))]]
    (is (rejects? text) (pr-str text))))
(deftest captured-fields-are-verified-and-snapshotted
  (let [text (str p/prefix (line "a" "x"))
        capture {:text text :byte-count (count text) :sha256 (p/sha256 text)
                 :path (java.nio.file.Path/of "Demo.lean" (make-array String 0)) :module ["Demo"]}
        parsed (p/captured-profile capture)]
    (is (= "Demo.lean" (:filename parsed)))
    (is (= ["Demo"] (:module parsed)))
    (is (= text (:text parsed)))
    (doseq [bad [(assoc capture :byte-count 0) (assoc capture :sha256 (apply str (repeat 64 "0")))
                 (assoc capture :path nil) (assoc capture :module ["../Demo"])
                 (assoc capture :text (StringBuilder. text)) (java.util.HashMap. capture)]]
      (is (thrown? clojure.lang.ExceptionInfo (p/captured-profile bad))))))
(deftest invalid-filesystem-limits-fail-before-reading
  (doseq [limit [nil 0 -1 16385 1.5]]
    (is (thrown? clojure.lang.ExceptionInfo (p/capture-source! {:max-bytes limit} ["NoRead"])))))
