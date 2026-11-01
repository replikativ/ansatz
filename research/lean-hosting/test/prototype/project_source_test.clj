(ns prototype.project-source-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [prototype.project-source :as p])
  (:import [java.nio.file Files Path]))

(def ^:dynamic *base* nil)
(use-fixtures :each
  (fn [test]
    (let [base (Files/createTempDirectory "ansatz-source-capture-"
                 (make-array java.nio.file.attribute.FileAttribute 0))]
      (binding [*base* base]
        (try (test)
          (finally
            (with-open [paths (Files/walk base (make-array java.nio.file.FileVisitOption 0))]
              (doseq [path (reverse (sort-by str (iterator-seq (.iterator paths))))]
                (Files/delete path)))))))))

(defn file [relative] (.resolve ^Path *base* ^String relative))
(defn directory! [relative]
  (Files/createDirectories (file relative) (make-array java.nio.file.attribute.FileAttribute 0)))
(defn write! [relative text]
  (let [path (file relative)]
    (Files/createDirectories (.getParent path) (make-array java.nio.file.attribute.FileAttribute 0))
    (spit (str path) text :encoding "UTF-8") path))
(defn error [f] (try (f) nil (catch Exception e e)))

(deftest package-shadowing
  (directory! "first/P")
  (write! "second/P/X.lean" "def x := 42")
  (write! "second/Q.lean" "def q := 1")
  (let [provider (p/provider [(file "first") (file "second")] 1024)
        selection (p/select-source provider ["P" "X"])]
    (is (= 0 (:root-index selection)))
    (is (= (file "first/P/X.lean") (:path selection)))
    (is (= "Selected package lacks source module" (.getMessage (error #(p/capture-source provider ["P" "X"])))))
    (is (nil? (p/select-source provider ["Unknown"])))
    (is (= 1 (:root-index (p/capture-source provider ["Q"]))))
    (write! "first/Q.lean" "-- package-file also shadows descendants")
    (write! "second/Q/X.lean" "def later := 2")
    (is (= 0 (:root-index (p/select-source provider ["Q" "X"]))))
    (is (some? (error #(p/capture-source provider ["Q" "X"]))))))

(deftest exact-content-and-bounds
  (write! "content/U.lean" "λ🦉")
  (let [provider (p/provider [(file "content")] 6)
        before (p/capture-source provider ["U"])]
    (is (= "λ🦉" (:text before))) (is (= 6 (:byte-count before)))
    (is (= 64 (count (:sha256 before))))
    (is (= (:sha256 before) (:sha256 (p/capture-source provider ["U"]))))
    (is (some? (error #(p/capture-source (p/provider [(file "content")] 5) ["U"]))))
    (write! "content/U.lean" "changed")
    (is (= "λ🦉" (:text before)))
    (let [after (p/capture-source (p/provider [(file "content")] 1024) ["U"])]
      (is (= "changed" (:text after))) (is (not= (:sha256 before) (:sha256 after))))
    (write! "content/Bad.lean" "placeholder")
    (with-open [out (java.io.FileOutputStream. (str (file "content/Bad.lean")))]
      (.write out (byte-array [(unchecked-byte 0xc3) (unchecked-byte 0x28)])))
    (is (some? (error #(p/capture-source provider ["Bad"]))))))

(deftest explicit-module-profile
  (directory! "content")
  (let [provider (p/provider [(file "content")] 1024)]
    (doseq [module [[] [".."] ["P.X"] ["/tmp"] ["x/y"] ["x\\y"] [1] [""]]]
      (is (some? (error #(p/select-source provider module)))))
    (is (some? (error #(p/provider [] 1024))))
    (is (some? (error #(p/provider [(file "content")] 0))))))

(deftest symlink-policy
  (write! "outside/Escape.lean" "outside")
  (directory! "linked")
  (Files/createSymbolicLink (file "linked/Escape.lean") (file "outside/Escape.lean")
                           (make-array java.nio.file.attribute.FileAttribute 0))
  (is (= "Selected source escapes its explicit root"
         (.getMessage (error #(p/capture-source (p/provider [(file "linked")] 1024) ["Escape"]))))))


(deftest explicit-roots-and-empty-utf8-file
  (directory! "root")
  (doseq [roots [[nil] [""] [false]]]
    (is (= "Source roots must be explicit nonempty paths"
           (.getMessage (error #(p/provider roots 1024))))))
  (is (some? (error #(p/provider [(file "root")] 67108865))))
  (write! "root/Empty.lean" "")
  (let [captured (p/capture-source (p/provider [(file "root")] 1) ["Empty"])]
    (is (= "" (:text captured)))
    (is (zero? (:byte-count captured)))
    (is (= "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" (:sha256 captured)))))

(deftest malformed-utf8-is-not-silently-replaced
  (directory! "root")
  (doseq [encoding [[0xc3 0x28] [0xc0 0x80] [0xed 0xa0 0x80] [0xf0 0x9f 0xa6]]]
    (with-open [out (java.io.FileOutputStream. (str (file "root/Bad.lean")))]
      (.write out (byte-array (map unchecked-byte encoding))))
    (is (= "Source is not valid UTF-8"
           (.getMessage (error #(p/capture-source (p/provider [(file "root")] 32) ["Bad"])))))))

(deftest symlink-within-canonical-root-captures-the-selected-content
  (write! "root/Actual.lean" "def actual := 7")
  (Files/createSymbolicLink (file "root/Alias.lean") (file "root/Actual.lean")
                           (make-array java.nio.file.attribute.FileAttribute 0))
  (let [captured (p/capture-source (p/provider [(file "root")] 1024) ["Alias"])]
    (is (= ["Alias"] (:module captured)))
    (is (= (file "root/Actual.lean") (:path captured)))
    (is (= "def actual := 7" (:text captured)))))
