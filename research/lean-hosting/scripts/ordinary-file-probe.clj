(require '[prototype.hosted-file :as ordinary-file]
         '[prototype.machine :as ordinary-machine])

(defn prepare-imported-file-probe
  "Use an ACTUALLY finalized and strictly associated import result. The caller
   keeps its owned imported Environment; compilation borrows it. Acquire one
   owner of the real initialized Lean.Options.empty global, without constructing
   an imitation Options or replacing the imported Environment. CATALOGUE must
   match the supplied session's pinned executable provenance."
  [{:keys [world session environment certificate] :as imported} catalogue]
  (assert (= :ok (:status imported)))
  (assert (instance? ansatz.kernel.Env (:env certificate)))
  (ordinary-machine/node world environment)
  (assert (identical? (:functions world) (:functions session)))
  (let [empty-options ["str" ["str" ["str" ["anonymous"] "Lean"] "Options"] "empty"]
        options (ordinary-machine/initialized-value world empty-options)]
    (ordinary-machine/node world options)
    {:world (ordinary-machine/retain world options 1)
     :session session :environment environment :options options :catalogue catalogue}))

(defn run-ordinary-file-probe
  "Compile and call an ordinary file from an explicit matching imported context.
   Each invocation starts at PREPARED, so callers can compare independent forks.
   Does not infer/import modules, run native compilers, or publish source modules."
  [prepared {:keys [path module root args initialization] :or {initialization :defer}}]
  (let [name #(ansatz.kernel.Name/mkStr ansatz.kernel.Name/ANONYMOUS_NAME %)]
    (ordinary-file/run-file prepared
      {:module-name (name module) :roots [(name root)] :path path
       :initialization initialization :calls [{:name (name root) :args args}]}
      {:install-options {:research-traps? true}})))
