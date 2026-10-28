(ns ansatz.export.parser-lifecycle-test
  "Scoped resource ownership around actual tiny parses/replays. Bundled bytes
   are modeled where noted; this does not replay the full bundled Init corpus."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]
            [ansatz.core :as core]
            [ansatz.bundle :as bundle]
            [ansatz.state :as state])
  (:import [ansatz.kernel ExprStore Name Expr TypeChecker Env]
           [java.io Closeable ByteArrayOutputStream]
           [java.util.zip GZIPOutputStream]))

(def tiny-export
  (str "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"P\"}}\n"
       "{\"ie\":0,\"sort\":0}\n"
       "{\"axiom\":{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}\n"))

(defn with-stores [f]
  (let [allocate parser/mk-parser-state
        stores (atom [])]
    (try
      (with-redefs [parser/mk-parser-state
                    (fn []
                      (let [st (allocate) ^ExprStore store (:exprs st)]
                        (.storeBvar store 127 0)
                        (is (bytes? (.readRaw store 127)))
                        (swap! stores conj store)
                        st))]
        (f stores))
      (finally (doseq [^ExprStore store @stores] (.close store))))))

(defn closed! [stores]
  (is (= 1 (count @stores)))
  (doseq [^ExprStore store @stores]
    (is (thrown? Exception (.readRaw store 127)))))

(defn with-file [f]
  (let [file (java.io.File/createTempFile "ansatz-parser-lifecycle-" ".ndjson")]
    (try
      (spit file tiny-export)
      (f (.getPath file))
      (finally (.delete file)))))

(defn usable! [^Env environment]
  ;; The full parsed expression remains usable after its backing file closes.
  (let [ci (.lookup environment (Name/fromString "P"))]
    (is (some? ci))
    (is (= (.type ci) (.inferType (TypeChecker. environment)
                                  (Expr/mkConst (Name/fromString "P") [] false))))))

(deftest scoped-state-detaches-a-real-kernel-environment-before-closing
  (with-stores
    (fn [stores]
      (let [environment (parser/with-parser-state
                          (parser/parse-ndjson-string tiny-export)
                          (fn [st] (:env (replay/replay (:decls st) :verify? true))))]
        (closed! stores)
        (usable! environment)))))

(deftest scoped-callback-failure-keeps-the-original-cause-and-closes
  (with-stores
    (fn [stores]
      (let [failure (AssertionError. "selected consumer failure")]
        (is (identical? failure
                        (try
                          (parser/with-parser-state
                            (parser/parse-ndjson-string tiny-export)
                            (fn [_] (throw failure)))
                          (catch Throwable cause cause))))
        (closed! stores)))))

(deftest cleanup-failure-never-replaces-an-existing-consumer-failure
  (let [failure (AssertionError. "original")
        cleanup (java.io.IOException. "cleanup")
        calls (atom 0)
        resource (reify Closeable (close [_] (swap! calls inc) (throw cleanup)))]
    (is (identical? failure
                    (try (parser/with-parser-state {:exprs resource} (fn [_] (throw failure)))
                         (catch Throwable cause cause))))
    (is (= [cleanup] (vec (.getSuppressed failure))))
    (is (= 1 @calls)))
  (let [failure (AssertionError. "same failure")
        resource (reify Closeable (close [_] (throw failure)))]
    (is (identical? failure
                    (try (parser/with-parser-state {:exprs resource} (fn [_] (throw failure)))
                         (catch Throwable cause cause))))
    (is (empty? (.getSuppressed failure)))))

(deftest success-closes-once-even-for-false-or-nil-and-surfaces-close-errors
  (doseq [value [false nil]]
    (let [calls (atom 0)
          resource (reify Closeable (close [_] (swap! calls inc)))]
      (is (= value (parser/with-parser-state {:exprs resource} (constantly value))))
      (is (= 1 @calls))))
  (let [cleanup (java.io.IOException. "cleanup")
        resource (reify Closeable (close [_] (throw cleanup)))]
    (is (identical? cleanup
                    (try (parser/with-parser-state {:exprs resource} (constantly :ok))
                         (catch Throwable cause cause))))))

(deftest public-file-load-and-replay-return-usable-results-with-closed-stores
  (with-file
    (fn [path]
      (doseq [load [parser/load-ndjson replay/replay-file]]
        (with-stores
          (fn [stores]
            (let [result (load path)]
              (closed! stores)
              (usable! (:env result)))))))))

(deftest public-unchecked-session-load-closes-before-installing-the-result
  (with-file
    (fn [path]
      (with-stores
        (fn [stores]
          (let [installed (atom nil)
                environment-cell (atom (Env.))]
            ;; core exposes the same atom as state; keep that alias intact in
            ;; the modeled installation, including load-export!'s return value.
            (with-redefs [state/ansatz-env environment-cell
                          core/ansatz-env environment-cell
                          core/setup-env! (fn [environment & _]
                                            (closed! stores)
                                            (reset! state/ansatz-env environment)
                                            (reset! installed environment))]
              (is (= 1 (:declarations (core/load-export! path :verify? false)))))
            (usable! @installed)))))))

(deftest replay-and-unchecked-session-failures-close-without-publishing
  (with-file
    (fn [path]
      (doseq [load [replay/replay-file #(core/load-export! % :verify? false)]]
        (with-stores
          (fn [stores]
            (let [failure (AssertionError. "replay failed")
                  installed (atom 0)]
              (with-redefs [replay/replay (fn [& _] (throw failure))
                            core/setup-env! (fn [_] (swap! installed inc))]
                (is (identical? failure (try (load path) (catch Throwable cause cause)))))
              (is (zero? @installed))
              (closed! stores))))))))

(deftest bundled-medium-replay-closes-its-parser-state
  ;; Actual parser and replay, replacing only the verified compressed input with
  ;; this tiny fixture; integrity/preflight of the real bundle is not claimed.
  (let [out (ByteArrayOutputStream.)]
    (with-open [gzip (GZIPOutputStream. out)]
      (.write gzip (.getBytes tiny-export java.nio.charset.StandardCharsets/UTF_8)))
    (with-stores
      (fn [stores]
        (with-redefs [bundle/verified-bytes (fn [_] (.toByteArray out))]
          (let [environment (#'core/bundled-medium-env false)]
            (closed! stores)
            (usable! environment)))))))

(deftest resolved-streaming-preserves-callback-error-when-store-close-also-fails
  (with-file
    (fn [path]
      (with-stores
        (fn [stores]
          (let [consume parser/with-parser-state
                failure (AssertionError. "stream callback failure")
                cleanup (java.io.IOException. "stream store close failure")]
            ;; ExprStore is final. Wrap only its cleanup to inject a failure
            ;; after closing the actual store; parsing/streaming stay real.
            (with-redefs [parser/with-parser-state
                          (fn [st f]
                            (consume
                             (assoc st :exprs
                                    (reify Closeable
                                      (close [_]
                                        (.close ^ExprStore (:exprs st))
                                        (throw cleanup))))
                             (fn [_] (f st))))]
              (is (identical? failure
                              (try
                                (parser/parse-ndjson-file-streaming
                                 path nil (fn [& _] (throw failure)))
                                (catch Throwable cause cause)))))
            (is (= [cleanup] (vec (.getSuppressed failure))))
            (closed! stores)))))))
