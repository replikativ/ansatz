(ns prototype.runtime-io
  "Replayable IO capabilities for the pinned Lean 4.33.1 runtime profile.
   Init/System/IO.lean:428 takes USize, followed by erased IO world in IR.
   lean.h lean_io_result_mk_ok transfers one owned field into ctor0; ByteArray
   uses LeanScalarArray tag248. runtime/io.cpp lean_io_get_random_bytes returns
   an empty array immediately for zero bytes, without consulting entropy.
   Init/System/IO.lean:951 getEnv returns BaseIO (Option String), directly;
   runtime/io.cpp lean_io_getenv rejects NUL names rather than truncating them.
   Hosts supply :take-entropy and :get-env; this module never reads host inputs.
   Missing/exhausted capabilities trap rather than invent native IO errors."
  (:require [prototype.scalar :as scalar]
            [prototype.runtime-string :as string]
            [clojure.string :as str]))

(def supported-symbols
  {"lean_io_get_random_bytes" {:arity 2}
   "lean_io_getenv" {:arity 2}
   "lean_get_stdin" {:arity 1} "lean_get_stdout" {:arity 1} "lean_get_stderr" {:arity 1}
   "lean_get_set_stdin" {:arity 2} "lean_get_set_stdout" {:arity 2} "lean_get_set_stderr" {:arity 2}})

(def stdio-symbols
  {"lean_get_stdin" [:stdin false] "lean_get_stdout" [:stdout false] "lean_get_stderr" [:stderr false]
   "lean_get_set_stdin" [:stdin true] "lean_get_set_stdout" [:stdout true] "lean_get_set_stderr" [:stderr true]})

(defn- fail [message data] (throw (ex-info message data)))

(defn- valid-string! [ops world value]
  ;; Reuse the exact UTF8 profile and bounded derived encoding cache.
  (string/evaluate ops world "lean_string_utf8_byte_size" [value])
  value)

(defn- get-env [ops world name]
  (let [name (string/string-value ops world name)]
    (valid-string! ops world name)
    (if (str/includes? name "\u0000") [world 0]
      (let [provider (:get-env ops)]
        (when-not (ifn? provider) (fail "Missing guest environment capability" {}))
        (let [result (provider world name)]
          (when-not (and (vector? result) (= 2 (count result)))
            (fail "Invalid environment provider result" {}))
          (let [[next-world value] result]
            (if (nil? value) [next-world 0]
              (do
                ;; The capability contract returns host text, not a borrowed
                ;; guest reference whose owner could accidentally be stolen.
                (when-not (string? value)
                  (fail "Environment provider must return host String or nil" {}))
                (valid-string! ops next-world value)
                (when (str/includes? value "\u0000")
                  (fail "Environment provider value contains NUL" {}))
                ((:allocate ops) next-world :ctor 1 [value])))))))))

(defn- take-entropy [ops world n]
  (if (zero? n) [world []]
    (let [provider (:take-entropy ops)]
      (when-not (ifn? provider)
        (fail "Missing guest entropy capability" {:requested n}))
      (let [result (provider world n)]
        (when-not (and (vector? result) (= 2 (count result)))
          (fail "Invalid entropy provider result" {:requested n}))
        (let [[next-world bytes] result]
          (when-not (sequential? bytes)
            (fail "Invalid entropy provider bytes" {:requested n}))
          ;; Bound realization even if a provider returns an infinite sequence.
          (let [bytes (vec (take (inc n) bytes))]
            (when-not (= n (count bytes))
              (fail "Entropy provider returned incorrect byte count"
                    {:requested n :actual (count bytes)}))
            (doseq [byte bytes] (scalar/integer! "uint8" byte))
            [next-world bytes]))))))

(defn- stream! [ops world stream]
  (when-not ((:ref? ops) stream) (fail "Expected guest FS.Stream reference" {:stream stream}))
  (let [node ((:node ops) world stream)]
    (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 6 (count (:fields node))))
      (fail "Malformed guest FS.Stream record" {:stream stream})) stream))

(defn- thread-key [ops world]
  (let [task (peek (:active ((:get-task-runtime ops) world)))]
    (if task (or (:thread-key ((:node ops) world task)) task) :main)))

(defn- current-stream [ops world channel]
  (let [context ((:get-stdio-runtime ops) world) key (thread-key ops world)]
    (if-let [stream (get-in context [:threads key channel])]
      (do (stream! ops world stream) [world stream key])
      (let [stream (get-in context [:defaults channel])]
        (when-not stream
          (fail "Missing guest standard stream capability; seed explicit guest FS.Stream defaults"
                {:channel channel :runtime-limit :unconfigured-stdio}))
        (stream! ops world stream)
        (let [world ((:retain ops) world stream 1)
              context (assoc-in context [:threads key channel] stream)]
          [((:set-stdio-runtime ops) world context) stream key])))))

(defn finish-task-streams
  "Async cooperative tasks own logical-thread stream slots. Sync continuations
   share their caller/producer slots. Release an async task's slots on completion;
   process default roots and other logical threads are untouched. No host IO."
  [ops world task thread]
  (if (not= task thread) world
    (let [context ((:get-stdio-runtime ops) world) streams (get-in context [:threads thread])]
      (if-not (seq streams) world
        (let [world ((:set-stdio-runtime ops) world (update context :threads dissoc thread))]
          (reduce (fn [world stream] ((:release ops) world stream 1)) world (vals streams)))))))

(defn- stdio [ops world symbol args]
  (let [[channel swap?] (get stdio-symbols symbol)
        replacement (when swap? (stream! ops world (first args)))
        [world previous key] (current-stream ops world channel)]
    (if swap?
      ;; Transfer the slot's previous owner to the caller and the argument's
      ;; owner into the slot. Getters return an additional retained owner.
      [((:set-stdio-runtime ops) world
         (assoc-in ((:get-stdio-runtime ops) world) [:threads key channel] replacement)) previous]
      [((:retain ops) world previous 1) previous])))

(defn evaluate
  "Evaluate [USize-or-borrowed-name, erased-world] against explicit inputs.
   Validate bytes before guest allocation; pure providers leave the caller's
   world unchanged on failure. Arbitrary provider side effects cannot roll back.
   Allocations transfer ownership into IO.Result.ok without extra retains.
   The prototype limits byte counts to the host vector index range. getEnv
   returns Option directly, preserving empty strings as Some, and validates
   well-formed Unicode. Provider values with NUL are outside the OS profile."
  [ops world symbol args]
  (let [spec (get supported-symbols symbol)]
    (when-not spec (fail "Unsupported IO runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args))
      (fail "IO runtime arity mismatch" {:symbol symbol :arity (count args)})))
  (cond
    (contains? stdio-symbols symbol) (stdio ops world symbol args)
    (= symbol "lean_io_getenv") (get-env ops world (first args))
    :else
  (let [n (scalar/integer! "usize" (first args))]
    (when (> n 2147483647)
      (fail "Entropy request exceeds supported host allocation" {:requested n}))
    (let [[world bytes] (take-entropy ops world (int n))
          [world array] ((:allocate ops) world :byte-array 248 [])
          node ((:node ops) world array)
          world ((:replace-node ops) world array (assoc node :bytes bytes))]
      ((:allocate ops) world :ctor 0 [array])))))
