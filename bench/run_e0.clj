;; Standalone E0 runner: boot mathlib fresh, run the re-find benchmark, exit.
;;   clj -J-Xmx8g -M bench/run_e0.clj
(load-file "bench/e0_refind.clj")
(println "recall-trie:" (some? @ansatz.core/ansatz-discr-trie)
         "| simp-trie:" (some? @ansatz.core/ansatz-simp-trie))
(run-e0!)
(shutdown-agents)
