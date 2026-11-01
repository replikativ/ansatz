;; Centralized configuration defaults for Ansatz.
;;
;; All values are dynamic vars and can be rebound per-thread with `binding`.

(ns ansatz.config
  "Centralized configuration defaults for fuel, depth limits, and
   candidate limits used throughout the Ansatz tactic and kernel layers.
   All values are dynamic vars that can be overridden via `binding`.")

(def ^:dynamic *lean-matchers*
  "Retain named, kernel-checked matchers during supported definition elaboration.
   False selects expression-only elaboration with matcher values inlined; all
   match expressions use the same Meta.Match compiler."
  true)

(def ^:dynamic *lean-structural-matchers*
  "Compile recursive matches with `brecOn` and generated matchers."
  true)

;; -- Kernel fuel --
(def ^:dynamic *default-fuel*
  "Default fuel for interactive Java TypeChecker operations (20M steps).
   Imported-store verification uses its own higher verifier default."
  20000000)

(def ^:dynamic *high-fuel*
  "High fuel for complex proofs requiring extra reduction steps (50M steps)."
  50000000)

;; -- WHNF limits --
(def ^:dynamic *max-whnf-depth*
  "Maximum recursion depth for WHNF reduction."
  512)

;; -- Instance synthesis --
(def ^:dynamic *synth-max-result-size*
  "Lean's `synthInstance.maxSize`: the maximum number of instances used to construct an answer
   (answers of this size or more are dropped)."
  128)

(def ^:dynamic *synth-max-steps*
  "The resource bound of one instance-synthesis problem: generate/resume steps of the tabled
   resolution — ansatz's counterpart of Lean's `synthInstance.maxHeartbeats` (which counts
   allocations, and so has no portable equivalent). Exceeding it is an error, as in Lean."
  10000)

;; -- Simp --
(def ^:dynamic *max-simp-steps*
  "Maximum number of simplification steps before erroring out."
  100000)

;; -- Grind --
(def ^:dynamic *grind-debug*
  "When true, print exceptions caught during grind sub-tactic dispatch."
  false)

(def ^:dynamic *grind-splits*
  "Maximum number of case splits in one grind proof-search branch (Lean's `Grind.Config.splits`,
   default 9). Normalization splits are not counted in Lean either."
  9)

(def ^:dynamic *grind-timeout-ms*
  "Wall-clock budget for one `grind` call; on expiry it fails with a tactic error instead of
   running on. nil disables it."
  20000)

;; -- Custom simprocs --
(def ^:dynamic *simprocs*
  "Vector of user-registered simproc functions.
   Each simproc is (fn [st expr] -> SimpResult-or-nil).
   Built-in simprocs (Nat/Int/decide) are always tried first;
   these are tried afterwards."
  [])
