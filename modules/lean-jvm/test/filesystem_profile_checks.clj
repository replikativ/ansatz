(ns ansatz-lean-jvm-filesystem-profile-checks
  "Synthetic filesystem authority/profile models; not native source evidence."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.capabilities :as caps] [ansatz.lean.jvm.ir :as ir]
            [clojure.java.io :as io])
  (:import [ansatz.lean.jvm ReadOnlyFiles] [java.nio.file Files Path]
           [java.nio.file.attribute FileAttribute] [java.lang.reflect InvocationTargetException]))
(defn name-of [text]
  (reduce (fn [parent part] ["str" parent part]) ["anonymous"] (.split ^String text "\\.")))
(def specifications
  [["System.FilePath.metadata" "lean_io_metadata" "object" ["object" "void"] [true false]]
   ["IO.FS.Handle.mk" "lean_io_prim_handle_mk" "object" ["object" "uint8" "void"] [true false false]]
   ["IO.FS.Handle.read" "lean_io_prim_handle_read" "object" ["tobject" "usize" "void"] [true false false]]
   ["IO.FS.Handle.getLine" "lean_io_prim_handle_get_line" "object" ["tobject" "void"] [true false]]
   ["IO.FS.Handle.write" "lean_io_prim_handle_write" "object" ["tobject" "object" "void"] [true true false]]
   ["IO.FS.Handle.putStr" "lean_io_prim_handle_put_str" "object" ["tobject" "object" "void"] [true true false]]
   ["IO.FS.Handle.flush" "lean_io_prim_handle_flush" "object" ["tobject" "void"] [true false]]
   ["IO.FS.Handle.rewind" "lean_io_prim_handle_rewind" "object" ["tobject" "void"] [true false]]
   ["IO.FS.Handle.truncate" "lean_io_prim_handle_truncate" "object" ["tobject" "void"] [true false]]
   ["IO.FS.Handle.isTty" "lean_io_prim_handle_is_tty" "uint8" ["tobject" "void"] [true false]]])
(defn row [[label symbol result types borrowed]]
  {"kind" "decl" "name" (name-of label) "sourceModule" (name-of "Init.System.IO")
   "runtime" {"role" "ordinary" "initializer" nil "initializationAction" nil} "redirect" nil
   "ir" {"extern" {"f" (name-of label) "type" result
                     "xs" (mapv (fn [index type borrow] {"x" {"idx" (inc index)} "ty" type "borrow" borrow})
                                (range) types borrowed)
                     "ext" {"entries" [{"standard" {"backend" (name-of "all") "fn" symbol}}]}}}})
(defn refused? [basis value]
  (try (caps/check-rows! basis [value]) false (catch clojure.lang.ExceptionInfo _ true)))
(deftest actual-abi-requires-distinct-explicit-filesystem-profile
  (let [basis (ir/linked-basis)]
    (is (= :task-free-captured-output-v1 (:profile (caps/check-rows! basis []))))
    (is (false? (:filesystem-required (caps/check-rows! basis []))))
    (doseq [spec specifications]
      (let [profile (caps/check-rows! basis [(row spec)])]
        (is (= :task-free-regular-files-v2 (:profile profile)))
        (is (true? (:filesystem-required profile)))
        (is (= :filesystem (:family (first (vals (:externs profile))))))))))
(deftest symbols-and-display-names-do-not-mint-canonical-runtime-authority
  (let [basis (ir/linked-basis)]
    (doseq [spec specifications :let [original (row spec)]]
      (is (refused? basis (assoc original "sourceModule" (name-of "Application"))))
      (is (refused? basis (assoc-in original ["runtime" "role"] "initializer")))
      (is (refused? basis (assoc-in original ["runtime" "initializer"] (name-of "injected"))))
      (is (refused? basis (assoc-in original ["runtime" "initializationAction"] (name-of "injected"))))
      (is (refused? basis (assoc original "redirect" {"name" (name-of "replacement")})))
      (is (refused? basis (assoc-in original ["ir" "extern" "xs" 0 "borrow"] false)))
      (is (refused? basis (assoc-in original ["ir" "extern" "xs" (dec (count (nth spec 3))) "ty"] "erased"))))
    (let [original (row (second specifications))
          ambiguous ["str" ["str" ["anonymous"] "IO.FS.Handle"] "mk"]]
      (is (refused? basis (-> original (assoc "name" ambiguous) (assoc-in ["ir" "extern" "f"] ambiguous)))))))
(defn- method-zero [value method]
  (.invoke (.getMethod (class value) method (make-array Class 0)) value (object-array 0)))
(defn- failure [action]
  (try (action) nil
    (catch Throwable error
      (loop [error error]
        (if (instance? InvocationTargetException error) (recur (.getCause ^Throwable error)) error)))))
(defn- with-root [test]
  (let [parent (.toAbsolutePath (.toPath (io/file "temp_files")))
        _ (Files/createDirectories parent (make-array FileAttribute 0))
        root (Files/createTempDirectory parent "filesystem-authority-" (make-array FileAttribute 0))]
    (try (test root)
      (finally (Files/delete root)))))
(defn- witness-bytes []
  (with-open [input (io/input-stream (io/resource "META-INF/ansatz-lean-jvm/filesystem-layouts.jsonl"))]
    (.readNBytes input 131073)))
(defn- install-files! [engine files]
  (.invoke (.getMethod (class engine) "installFiles"
                       (into-array Class [(class files) (class (byte-array 0))]))
           engine (object-array [files (witness-bytes)])))
(defn- header-context [rows]
  (let [base (assoc (ir/prepare-host-program (ir/linked-basis) [] []) :initializing false)
        source (ir/source-binding base (Object.))
        ;; This source token/hash is a synthetic model, never native byte authority.
        headers (mapv #(ir/declaration-header source % (apply str (repeat 64 "0"))) rows)]
    (ir/register-headers base headers)))

(deftest install-preflights-exact-header-authority-before-claiming-session
  (with-root
    (fn [root]
      (let [original (row (first specifications))
            quoted ["str" ["str" ["anonymous"] "System.FilePath"] "metadata"]]
        (doseq [bad [(-> original (assoc "name" quoted) (assoc-in ["ir" "extern" "f"] quoted))
                     (assoc original "sourceModule" (name-of "Application"))]]
          (let [ctx (header-context [bad])]
            (with-open [files (ir/file-session ctx (ReadOnlyFiles/root root))
                        engine (ir/machine ctx)]
              (let [before (method-zero files "stats") rejected (failure #(install-files! engine files))]
                (is (instance? IllegalArgumentException rejected))
                (is (re-find #"canonical Headers" (or (some-> ^Throwable rejected .getMessage) "")))
                (is (= before (method-zero files "stats")))
                ;; A successful caller claim proves installation never consumed it.
                (.invoke (.getMethod (class files) "claimOwner" (into-array Class [Object]))
                         files (object-array [(Object.)]))
                (is (zero? (.operations (method-zero files "stats"))))))))))))

(deftest valid-cached-filesystem-headers-have-no-effects-and-refuse-fork
  (with-root
    (fn [root]
      (let [ctx (header-context (mapv row specifications))]
        (with-open [files (ir/file-session ctx (ReadOnlyFiles/root root))
                    engine (ir/machine ctx)]
          (install-files! engine files)
          (is (zero? (.operations (method-zero files "stats"))))
          (is (zero? (.liveHandles (method-zero files "stats"))))
          (let [rejected (failure #(method-zero engine "eagerFork"))]
            (is (instance? IllegalArgumentException rejected))
            (is (re-find #"Filesystem sessions cannot be forked" (or (some-> ^Throwable rejected .getMessage) "")))))))))

(deftest later-raw-extern-cannot-pass-an-empty-cached-header-slot
  (with-root
    (fn [root]
      (let [base (header-context [])]
        (with-open [files (ir/file-session base (ReadOnlyFiles/root root))
                    engine (ir/machine base)]
          (install-files! engine files)
          ;; Raw extension deliberately has no Header; no immutable field mutation.
          (let [extended (ir/extend-program base [(row (first specifications))])]
            (ir/install-program! extended engine)
            (let [rejected (failure #(ir/call extended engine "System.FilePath.metadata" ["." (long 0)]))]
              (is (instance? IllegalArgumentException rejected))
              (is (re-find #"installed source Header" (or (some-> ^Throwable rejected .getMessage) "")))
              (is (zero? (.operations (method-zero files "stats"))))
              (is (zero? (.liveHandles (method-zero files "stats")))))))))))

(defn check! [] (run-tests 'ansatz-lean-jvm-filesystem-profile-checks))
