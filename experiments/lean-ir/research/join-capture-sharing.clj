(ns join-capture-sharing
  "REPL-only consecutive join capture sharing. Stock interpreter, one thread,
   no custom helper callbacks. Scoped root replacement is not production code."
  (:refer-clojure :exclude [run!])
  (:require [prototype.mutable :as u]
            [prototype.machine :as m]))

(defn run!
  ([machine fuel] (run! machine fuel nil))
  ([machine fuel census]
   (let [capture u/capture-join!
         ctl @(ns-resolve 'prototype.mutable 'ctl)
         ;; Machine, active register array, expected next PC, read-only snapshot.
         cache (object-array 4)]
     (with-redefs
       [u/join!
        (fn [s id params body]
          (let [pc (ctl s 0) locals (ctl s 1)
                reuse? (and (identical? s (aget cache 0))
                            (identical? locals (aget cache 1))
                            (identical? pc (aget cache 2)))
                snapshot (if reuse? (aget cache 3) (aclone ^objects locals))]
            (when census
              (vswap! census update (if reuse? :shared :cloned) (fnil inc 0)))
            (capture s id params body snapshot)
            (aset cache 0 s) (aset cache 1 locals)
            (aset cache 2 (nth pc 4 nil)) (aset cache 3 snapshot)))]
       ;; The cache dies on every return, pause, suspension or exception. No
       ;; array/state is retained in a program cache or across public entries.
       (u/run! machine fuel)))))
