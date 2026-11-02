(ns engine-support.fixtures
  (:require [clojure.java.io :as io])
  (:import [java.security MessageDigest]
           [java.math BigInteger]))

(defn sha256 [path]
  (let [digest (MessageDigest/getInstance "SHA-256")]
    (with-open [input (io/input-stream path)]
      (let [buffer (byte-array 8192)]
        (loop []
          (let [n (.read input buffer)]
            (when (pos? n) (.update digest buffer 0 n) (recur))))))
    (format "%064x" (BigInteger. 1 (.digest digest)))))
