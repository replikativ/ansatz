(ns ansatz.state
  "The global kernel state — the current Env and instance index — as REPL-convenience atoms.
   A dependency-free leaf (like ansatz.surface.ingest holds the shared registries) so namespaces
   extracted from ansatz.core (codegen, wf, …) can read and mutate the live env without a
   core↔X load cycle. ansatz.core re-exports these; a/ansatz-env stays the wandler-facing handle.")

(defonce ^{:doc "The current kernel Env (a value), as an atom. nil until (ansatz/init!)."}
  ansatz-env (atom nil))
(defonce ^{:doc "The current instance index (name → instances), as an atom."}
  ansatz-instance-index (atom nil))
