(ns imported-frontend-setup-v4
  "Fixed actual Prelude import header setup; not kernel association authority."
  (:require [sequential-frontend-probe :refer :all]
            [java-ir-baseline :as j]
            [ansatz.research.ir.kernel-projection :as projection]
            [ansatz.kernel.name :as kernel-name]))
(defn validate-prelude-imports! [s imports]
  ;; Pinned Lean.Elab.HeaderSyntax.imports produces Import(Name, three Bool bytes).
  ;; Compare the parsed requests, not textual prefixes or rendered Name strings.
  (assert (= 1 (j/request-value imports "arraySize")) "Exactly one Prelude request required")
  (let [request (aget ^objects (fields s imports) 0)
        f (ctor! s request 0 1)
        flags (mapv #(Byte/toUnsignedInt %) (scalars s request))
        scope (projection/open-projector (ctx s) (engine s)
                {:max-nodes 256 :deadline-nanos (+ (System/nanoTime) 5000000000)})]
    (try
      (assert (= [0 1 0] flags) "Parsed import flags differ from the admitted requested import")
      (assert (= (kernel-name/from-string "Init.Prelude")
                 (:value ((:projector scope) (:world scope) :name (aget ^objects f 0))))
              "Parsed module differs from the finalized import")
      (finally ((:close! scope))))))
(defn- setup-classic* [driver real-env text filename module-segments validate-imports! runtime-step!]
  (assert (and (vector? module-segments) (<= 1 (count module-segments) 256)
               (every? #(and (string? %) (seq %) (not (re-find #"[.\\/\u0000]" %))) module-segments)))
  (let [s (cond-> {:driver driver :owners (atom {}) :observations (atom []) :calls (atom []) :in-flight (atom nil)
           :deadline-nanos (+ (System/nanoTime) 60000000000)
           :limits {:instructions 3000000 :code-requests 3000 :turns 50000 :commands 3}
           :used (atom {:instructions 0 :code-requests 0 :turns 0 :commands 0})}
                   runtime-step! (assoc :runtime-step! runtime-step!))]
    (try
      ;; FIRST check: no guest call, retain or reflective allocation before this.
      (preflight-real-env! s real-env)
      (assert (= "idle" (j/phase (ctx s) (engine s))))
      (assert (:task-runtime (ctx s)) "Require explicit active synchronous runtime")
      (let [size (call! s "String.utf8ByteSize" [text])
            input (hold! s :input (call! s "Lean.Parser.mkInputContext._redArg" [text filename 1 size]))]
        (ctor! s input 0 4)
        (hold! s :header-result (call! s "Lean.Parser.parseHeader" [(facade-owner! s :input) 0]))
        (let [payload (aget ^objects (ctor! s (owned s :header-result) 0 1) 0)
              pair (ctor! s payload 0 2) rest (ctor! s (aget ^objects pair 1) 0 2)]
          (retain-as! s :header (aget ^objects pair 0))
          (retain-as! s :parser-state (aget ^objects rest 0))
          (retain-as! s :header-messages (aget ^objects rest 1)))
        (drop! s :header-result)
        (retain-as! s :header-messages-observation (owned s :header-messages))
        (assert (not (error-log? s :header-messages)) "Header diagnostics reported errors")
        (assert (not (bool! (call! s "Lean.Elab.HeaderSyntax.isModule" [(facade-owner! s :header)]))) "Module file outside fixed probe")
        (hold! s :prelude-stx (call! s "Lean.Syntax.getArg" [(facade-owner! s :header) 1]))
        (assert (not (bool! (call! s "Lean.Syntax.isNone" [(take-owner! s :prelude-stx)]))) "Actual prelude required")
        (assert (not (bool! (call! s "Lean.Elab.HeaderSyntax.isModule" [(facade-owner! s :header)])))
                "This fixed first profile requires Lean legacy/private mode")
        (hold! s :imports (call! s "Lean.Elab.HeaderSyntax.imports" [(facade-owner! s :header) 1]))
        (validate-imports! s (owned s :imports))
        (drop! s :imports)
        (drop! s :header)
        (hold! s :module-name (call! s "Lean.Name.mkStr1" [(first module-segments)]))
        (doseq [segment (rest module-segments)]
          (hold! s :module-segment (call! s "Lean.Name.mkStr1" [segment]))
          (hold! s :module-name (call! s "Lean.Name.appendCore"
                                [(take-owner! s :module-name) (take-owner! s :module-segment)])))
        (let [module-name (take-owner! s :module-name)]
          (j/retain! (ctx s) (engine s) real-env)
          (hold! s :environment (call! s "Lean.Environment.setMainModule" [real-env module-name])))
        (hold! s :options (call! s "Lean.Options.empty" []))
        (doseq [[prefix leaf] (concat [["Elab" "async"] ["debug" "skipKernelTC"]]
                                      (get (ctx s) :lab-false-bool-options []))]
          (let [name (call! s "Lean.Name.mkStr2" [prefix leaf])]
            (hold! s :options (call! s "Lean.Options.setBool" [(take-owner! s :options) name 0]))))
        ;; Strict native-kernel prototype: disable the TWO original native
        ;; resource limits through real guest options. VM/projection/checker
        ;; host budgets remain separately enforced and are not native counters.
        (doseq [option ["maxHeartbeats" "maxRecDepth"]]
          (let [name (call! s "Lean.Name.mkStr1" [option])
                nat-value-instance (call! s "Lean.KVMap.instValueNat" [])]
            (hold! s :options (call! s "Lean.Options.set" [0 nat-value-instance (take-owner! s :options) name 0]))))
        (hold! s :command-state (call! s "Lean.Elab.Command.mkState"
                                  [(take-owner! s :environment) (take-owner! s :header-messages) (take-owner! s :options)]))
        (let [ps (owned s :parser-state) f (ctor! s ps 0 1)]
          (assert (= 2 (alength ^bytes (scalars s ps))))
          (retain-as! s :command-pos (aget ^objects f 0)))
        (hold! s :commands (call! s "Array.emptyWithCapacity" [0 0]))
        (assemble-state! s)
        (hold! s :state-ref (call! s "ST.Prim.mkRef" [0 0 (take-owner! s :frontend-state) 0]))
        {:status :prepared :session s :initial-observation (snapshot! s 0)
         :adapter-allocations 1 :checked-declaration-established false})
      (catch Throwable error
        (failure s error)))))
(defn setup-prelude!
 ([driver real-env text filename]
  (setup-prelude! driver real-env text filename ["Hosted" "SequentialProbe"]))
 ([driver real-env text filename module-segments]
  (setup-classic* driver real-env text filename module-segments validate-prelude-imports! nil)))
