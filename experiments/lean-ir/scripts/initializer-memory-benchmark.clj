;; Actual pinned catalogue + initializer witness only; no guest/archive/ModuleData work.
(load-file "scripts/full-init-assembly-probe.clj")
(let [[input-path output-path implementation-path] *command-line-args*]
  (assert (and input-path output-path) "Usage: initializer-memory-probe.clj INPUT_JSON OUTPUT_JSON [PINNED_OLD_SOURCE]")
  (when implementation-path
    (assert (= "4f2a0dd44b1c1a2023df8efdc4465da7a9e46b73bf5331593e210e5a386460d0"
               (full-init-assembly-sha256 implementation-path)) "Historical implementation hash mismatch")
    (load-file implementation-path)))
(def initializer-memory-roots (atom nil))
(defn initializer-memory-used []
  (System/gc)
  (let [r (Runtime/getRuntime)] (- (.totalMemory r) (.freeMemory r))))
(let [capture (json/read-str (slurp "measurements/full-init-assembly.json") :key-fn keyword)
      _ (doseq [path (concat ["target/frontend-lean-module-index.edn" "target/lean-export-aliases.jsonl"
                             "target/module-initializer-symbols.json"] (:overlays full-init-assembly-paths))]
          (let [expected (get-in capture [:preparation-inputs-after-run (keyword path) :sha256])]
            (assert expected path)
            (assert (= expected (full-init-assembly-sha256 path)) path)))
      input (json/read-str (slurp (first *command-line-args*)) :key-fn keyword)
      _ (assert (= "c01bfd4403badf2f3cb10e1ad7ebdd2e256845d1c0337a8749f72c62ae398cf9"
                   (full-init-assembly-sha256 (first *command-line-args*))) "Benchmark input hash differs")
      index (:index-sha256 input)
      _ (assert (= index (:index-sha256 full-init-assembly-paths)))
      plans (into {} (map (juxt :module identity)) (:plans input))
      witness (json/read-str (slurp (:initializer-witness full-init-assembly-paths)) :key-fn keyword)
      options (full-initializers/options-from-witness plans witness)
      _ (reset! initializer-memory-roots {:input input :plans plans :witness witness :options options})
      before (initializer-memory-used)
      started (System/nanoTime)
      bindings (full-initializers/make-bindings options)
      elapsed (/ (- (System/nanoTime) started) 1e6)
      _ (swap! initializer-memory-roots assoc :bindings bindings)
      after (initializer-memory-used)
      summary {:scope :actual-initializer-binding-construction-only
               :catalogue-index index :plans (count plans)
               :witness-symbols (count (:symbols witness))
               :admitted-symbols (count (:initialized-symbols options))
               :retained-before-bytes before :retained-after-bytes after
               :retained-binding-delta-bytes (- after before) :construction-ms elapsed
               :guest-executed false :archive-restored false :module-data-opened false}]
  (spit (str (second *command-line-args*) ".construction.json") (json/write-str summary))
  (println (json/write-str summary)))

(let [options (:options @initializer-memory-roots)
      binding (get-in @initializer-memory-roots [:bindings "lean_run_mod_init_core"])
      guards (set (map (juxt :module :phase) (vals (:initialized-symbols options))))
      base (assoc (full-machine/world {}) :initialized-modules guards)
      started (System/nanoTime)
      available (reduce (fn [n symbol]
                          (let [[world value] ((:handler binding) nil base [symbol full-machine/erased])
                                fields (:fields (full-machine/node world value))]
                            (assert (contains? #{[0] [1]} fields))
                            (full-machine/release world value 1)
                            (+ n (first fields))))
                        0 (keys (:initialized-symbols options)))
      summary {:scope :actual-initializer-host-queries-no-guest
               :queries (count (:initialized-symbols options)) :world-guards (count guards)
               :available available :elapsed-ms (/ (- (System/nanoTime) started) 1e6)}]
  (spit (second *command-line-args*) (json/write-str summary))
  (println (json/write-str summary)))

(reset! initializer-memory-roots nil)
(println {:retained-after-cleanup (initializer-memory-used)})
(shutdown-agents)
(System/exit 0)
