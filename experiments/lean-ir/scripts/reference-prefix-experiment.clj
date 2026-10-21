;; Definitions only; no redefinition, invocation, threads or ownership transfer.
;; This is an experimental callable alternative, NOT an installed runtime hook.
(ns prototype.reference-prefix-draft
  (:require [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]))

(defn run-boundary
  "Opt-in persistent prefix before MUTABLE execution. JVM/reference retain their
   existing paths. Prefix instructions count against the same supplied fuel.
   No handler executes here and no session/cache/function is replaced."
  [session world fuel prefix-limit]
  (when-not (and (integer? fuel) (<= 0 fuel Long/MAX_VALUE)
                (integer? prefix-limit) (<= 0 prefix-limit Long/MAX_VALUE))
    (throw (ex-info "Invalid experimental reference-prefix budget" {})))
  (case (:backend session)
    :reference (m/run world fuel)
    :jvm (u/freeze (lazy/run! (:program session) (u/thaw world) fuel))
    :mutable
    (if (and (= :running (:status world)) (pos? prefix-limit))
      (let [prefix-fuel (min fuel prefix-limit)
            prefix (m/run world prefix-fuel)]
        (if (and (= :paused (:status prefix)) (> fuel prefix-fuel))
          ;; m/run paused after EXACTLY prefix-fuel instructions. Resume this
          ;; persistent state; the original input is never replayed.
          (u/freeze (u/run! (u/thaw (m/resume prefix m/erased)) (- fuel prefix-fuel)))
          prefix))
      (u/freeze (u/run! (u/thaw world) fuel)))))
