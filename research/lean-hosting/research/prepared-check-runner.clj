;; Bounded checks only: no Init, Source, frontend or external Lean process.
;; Run once in a fresh JVM, or load once in the experiment REPL.
(doseq [file ["prepared-interpreter" "prepared-fused" "prepared-native-ops"
              "prepared-runtime" "prepared-interpreter-checks" "prepared-runtime-checks"]]
  (load-file (str "research/" file ".clj")))
(prn {:ordinary (prepared-interpreter-checks/check!)
      :fused (prepared-interpreter-checks/check!
               {:prepare-program prepared-fused/prepare-program
                :step! prepared-fused/step! :run! prepared-fused/run!})
      :runtime (prepared-runtime-checks/check!)})
