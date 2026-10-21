(ns prototype.frontend-smoke
  "Opt-in native-assisted file loading check. These results do not claim a
  hosted parser/elaborator. Run experiment in a REPL; -main is CLI-only."
  (:require [prototype.bootstrap :as bootstrap]
            [prototype.interop :as interop]
            [prototype.compact-bench :as provenance]
            [clojure.data.json :as json]
            [clojure.java.io :as io]))

(def bindings
  {"ansatz_host_transform" {:arguments [:nat] :result :nat :fn (fn [_ x] (inc x))}
   "ansatz_host_apply" {:arguments [:closure :nat] :result :nat
                       :fn (fn [{:keys [invoke]} f x] (+ (invoke f [x]) (invoke f [x])))}})

(defn experiment [exporter]
  (when-not (and exporter (.isFile (io/file exporter)))
    (throw (ex-info "Supply a matching lean4export executable" {})))
  (let [interop (bootstrap/load-file!
                 {:module "InteropProbe"
                  :roots ["InteropProbe.identity" "InteropProbe.callHost" "InteropProbe.roundTrip" "InteropProbe.applyCallback"]
                  :bindings bindings :kernel-exporter exporter})
        frontend (bootstrap/load-file!
                  {:module "FrontendProbe" :roots ["FrontendProbe.answer"]
                   :bindings bindings :kernel-exporter exporter})
        values {:identity ((interop/function interop "InteropProbe.identity") 42)
                :host ((interop/function interop "InteropProbe.callHost") 42)
                :roundtrip ((interop/function interop "InteropProbe.roundTrip") 42)
                :host-callback ((interop/function interop "InteropProbe.applyCallback")
                                 (interop/function-ref "InteropProbe.hostTransform") 42)
                :macro ((interop/function frontend "FrontendProbe.answer") 42)}
        paths ["lean/InteropProbe.lean" "lean/FrontendProbe.lean" "lean/Export.lean"
               "src/prototype/bootstrap.clj" "src/prototype/interop.clj"
               "src/prototype/frontend_smoke.clj" "src/prototype/machine.cljc"
               "src/prototype/mutable.clj" "src/prototype/import_ir.clj"
               "src/prototype/block_compile.clj" "src/prototype/lazy_runtime.clj"]]
    (when-not (= values {:identity 42 :host 43 :roundtrip 84 :host-callback 43 :macro 43})
      (throw (ex-info "Native-assisted smoke mismatch" {:values values})))
    {:toolchain bootstrap/toolchain :frontend :native-bootstrap :values values
     :kernel-checks {:interop (:kernel-stats interop) :macro (:kernel-stats frontend)}
     :source-sha256 (into {} (map (fn [p] [p (provenance/sha256 p)]) paths))
     :artifacts (into {} (for [p ["target/bootstrap/InteropProbe.jsonl" "target/bootstrap/InteropProbe.ndjson"
                                 "target/bootstrap/FrontendProbe.jsonl" "target/bootstrap/FrontendProbe.ndjson"]]
                          [p (provenance/sha256 p)]))
     :limitations ["Native Lean parses, elaborates, expands macros and exports IR"
                   "Ansatz kernel rechecks exported declarations; IR compilation and host implementations are not proved"
                   "Only linked small-Nat/closure programs are supported, not arbitrary Lean files"
                   "Host callbacks are synchronous and cannot escape their invocation"
                   "Dependency build orchestration, module initialization and hosted frontend remain future work"]}))

(defn -main [& [exporter]]
  (println (json/write-str (experiment (or exporter (System/getenv "LEAN4EXPORT_BIN")))))
  (shutdown-agents))
