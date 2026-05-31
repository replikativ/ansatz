(ns ansatz.tools.kernel-trace
  "Helpers for tracing kernel checks and comparing trace streams."
  (:require [ansatz.export.storage :as storage]
            [ansatz.kernel.name :as ansatz-name]
            [clojure.data.json :as json]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str])
  (:import [ansatz.kernel ConstantInfo Expr TypeChecker]
           [java.io FileWriter]))

(defn- usage []
  (println "Usage:")
  (println "  clojure -M -m ansatz.tools.kernel-trace trace-ansatz <store> <branch> <decl> <out> [fuel]")
  (println "  clojure -M -m ansatz.tools.kernel-trace trace-lean <lean-root> <lean-file> <decl> <out> [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace trace-mathlib <store> <branch> <decl> <lean-root> <lean-file> <out-dir> [fuel] [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace trace-batch <store> <branch> <lean-root> <manifest> <out-dir> [fuel] [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace trace-batch-summary <store> <branch> <lean-root> <manifest> <out-dir> [fuel] [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace trace-batch-summary-strict <store> <branch> <lean-root> <manifest> <out-dir> [fuel] [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace curate-batch <store> <branch> <lean-root> <manifest> <trace-out-dir> <report-dir> [fuel] [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace curate-batch-grouped <store> <branch> <lean-root> <manifest> <trace-out-dir> <report-dir> [fuel] [lean-bin|lake]")
  (println "  clojure -M -m ansatz.tools.kernel-trace compare <left> <right> [max-mismatches] [window]")
  (println "  clojure -M -m ansatz.tools.kernel-trace compare-normalized-fvars <left> <right> [max-mismatches] [window]")
  (println "  clojure -M -m ansatz.tools.kernel-trace compare-semantic <left> <right> [max-mismatches] [window]"))

(defn- read-json-lines [path]
  (with-open [r (io/reader path)]
    (doall
     (map #(json/read-str % :key-fn keyword)
          (line-seq r)))))

(defn- read-raw-lines [path]
  (with-open [r (io/reader path)]
    (vec (line-seq r))))

(defn- slice-decl-lines [lines decl-name]
  (let [decl-idxs (keep-indexed (fn [i x] (when (:decl x) i)) lines)]
    (if (and decl-name (seq decl-idxs))
      (if-let [start (first (filter #(= decl-name (:decl (nth lines %))) decl-idxs))]
        (let [end (or (first (filter #(< start %) decl-idxs))
                      (count lines))]
          (subvec (vec lines) start end))
        [])
      lines)))

(defn- slice-decl-raw-lines [raw-lines parsed-lines decl-name]
  (let [decl-idxs (keep-indexed (fn [i x] (when (:decl x) i)) parsed-lines)]
    (if-let [start (first (filter #(= decl-name (:decl (nth parsed-lines %))) decl-idxs))]
      (let [end (or (first (filter #(< start %) decl-idxs))
                    (count raw-lines))]
        (subvec raw-lines start end))
      [])))

(defn- event-lines
  ([path]
   (event-lines path nil))
  ([path decl-name]
   (-> (read-json-lines path)
       vec
       (slice-decl-lines decl-name)
       (->> (filter :by)
            vec))))

(defn- trace-file-analysis
  "Classify structural properties of a trace file after applying the same
   declaration slicing used for event comparison. Multiple event sequence
   starts usually mean the Lean substring filter captured more than the target
   declaration or a stale type_checker kept the active trace file."
  ([path]
   (trace-file-analysis path nil))
  ([path decl-name]
   (let [lines (vec (read-json-lines path))
         sliced (slice-decl-lines lines decl-name)
         events (vec (filter :by sliced))
         decl-markers (vec (keep :decl sliced))
         seq-zero-events (->> events
                              (keep-indexed
                               (fn [idx ev]
                                 (when (zero? (long (or (:s ev) -1)))
                                   {:idx idx
                                    :event (select-keys ev [:d :l :r :res :by])})))
                              vec)
         distinct-decls (vec (distinct decl-markers))
         unexpected-decls (if (seq decl-name)
                            (vec (remove #{decl-name} distinct-decls))
                            [])]
     {:decl-markers decl-markers
      :distinct-decl-markers distinct-decls
      :unexpected-decl-markers unexpected-decls
      :event-sequences (count seq-zero-events)
      :sequence-starts seq-zero-events
      :ambiguous? (or (> (count distinct-decls) 1)
                      (seq unexpected-decls)
                      (> (count seq-zero-events) 1))})))

(defn- event-view [ev]
  (select-keys ev [:d :l :r :res :by]))

(defn- normalize-fvars [s]
  (when s
    (str/replace s #"_kernel_fresh\.\d+" "_kernel_fresh._")))

(defn- ordered-pair [a b]
  (if (pos? (compare a b)) [b a] [a b]))

(defn- normalize-level-max-step [s]
  (-> s
      (str/replace #"max 0 ([A-Za-z0-9_]+)" "$1")
      (str/replace #"max ([A-Za-z0-9_]+) 0" "$1")
      (str/replace #"max 1 \(succ ([^)]+)\)" "succ $1")
      (str/replace #"max \(succ ([^)]+)\) 1" "succ $1")
      (str/replace #"max \(succ \(max ([A-Za-z0-9_]+) ([A-Za-z0-9_]+)\)\) \(succ ([A-Za-z0-9_]+)\)"
                   (fn [[_ a b c]]
                     (let [[x y] (ordered-pair a b)]
                       (if (or (= c a) (= c b))
                         (str "succ (max " x " " y ")")
                         (str "max (succ (max " x " " y ")) (succ " c ")")))))
      (str/replace #"max \(succ ([A-Za-z0-9_]+)\) \(succ \(max ([A-Za-z0-9_]+) ([A-Za-z0-9_]+)\)\)"
                   (fn [[_ c a b]]
                     (let [[x y] (ordered-pair a b)]
                       (if (or (= c a) (= c b))
                         (str "succ (max " x " " y ")")
                         (str "max (succ " c ") (succ (max " x " " y "))")))))
      (str/replace #"max \(succ ([A-Za-z0-9_]+)\) \(succ ([A-Za-z0-9_]+)\)"
                   (fn [[_ a b]]
                     (let [[x y] (ordered-pair a b)]
                       (str "succ (max " x " " y ")"))))
      (str/replace #"succ \(max ([A-Za-z0-9_]+) ([A-Za-z0-9_]+)\)"
                   (fn [[_ a b]]
                     (let [[x y] (ordered-pair a b)]
                       (str "succ (max " x " " y ")"))))
      (str/replace #"max ([A-Za-z0-9_]+) ([A-Za-z0-9_]+)"
                   (fn [[_ a b]]
                     (let [[x y] (ordered-pair a b)]
                       (str "max " x " " y))))))

(defn- normalize-level-max [s]
  (when s
    (loop [cur s]
      (let [nxt (normalize-level-max-step cur)]
        (if (= cur nxt) cur (recur nxt))))))

(defn- normalize-trace-text [s]
  (some-> s normalize-fvars normalize-level-max))

(defn- event-view-normalized-fvars [ev]
  (-> (event-view ev)
      (update :l normalize-trace-text)
      (update :r normalize-trace-text)))

(defn- reflexive-quick? [view]
  (and (= "quick" (:by view))
       (true? (:res view))
       (= (:l view) (:r view))))

(defn- nat-lor-hor-wrapper? [view]
  (and (= "lazy_delta" (:by view))
       (true? (:res view))
       (let [text (str (:l view) " " (:r view))]
         (and (str/includes? text "Nat.lor")
              (str/includes? text "HOr.hOr")))))

(defn- semantic-epsilon-kind [view]
  (cond
    (reflexive-quick? view) :reflexive-quick
    (nat-lor-hor-wrapper? view) :nat-lor-hor-wrapper
    :else nil))

(defn- semantic-epsilon? [view]
  (boolean (semantic-epsilon-kind view)))

(defn- trunc-prefix [s]
  (when (and (string? s) (str/ends-with? s "..."))
    (subs s 0 (- (count s) 3))))

(defn- compatible-field? [a b]
  (or (= a b)
      (let [ap (trunc-prefix a)
            bp (trunc-prefix b)]
        (cond
          (and ap bp) (or (str/starts-with? ap bp)
                          (str/starts-with? bp ap))
          ap (str/starts-with? b ap)
          bp (str/starts-with? a bp)
          :else false))))

(defn- phase-compatible-view? [a b]
  (and (true? (:res a))
       (true? (:res b))
       (= (:d a) (:d b))
       (= #{(:by a) (:by b)} #{"lazy_delta" "whnfcore2"})
       (compatible-field? (:l a) (:l b))
       (compatible-field? (:r a) (:r b))))

(defn- compatible-view? [a b]
  (and (= (:d a) (:d b))
       (= (:res a) (:res b))
       (or (= (:by a) (:by b))
           (phase-compatible-view? a b))
       (compatible-field? (:l a) (:l b))
       (compatible-field? (:r a) (:r b))))

(defn- by-histogram [events]
  (reduce (fn [m ev] (update m (:by ev) (fnil inc 0))) {} events))

(defn- contains-mdata-text? [x]
  (cond
    (string? x) (str/includes? x "mdata(")
    (map? x) (some contains-mdata-text? (vals x))
    (sequential? x) (some contains-mdata-text? x)
    :else false))

(defn- source-mdata-mismatch?
  "True when a strict mismatch is explained by Lean source metadata that is
   absent from the imported declaration being checked by Ansatz."
  [result semantic-ok?]
  (and (not semantic-ok?)
       (zero? (long (or (get-in result [:ansatz :type-mdata]) 0)))
       (zero? (long (or (get-in result [:ansatz :value-mdata]) 0)))
       (contains-mdata-text? (get-in result [:semantic :first-mismatch]))))

(defn- mismatch-indices [left right]
  (let [common (min (count left) (count right))]
    (->> (range common)
         (filter (fn [i]
                   (not= (event-view (nth left i))
                         (event-view (nth right i)))))
         vec)))

(defn- mismatch-indices-by [view-fn left right]
  (let [common (min (count left) (count right))]
    (->> (range common)
         (filter (fn [i]
                   (not= (view-fn (nth left i))
                         (view-fn (nth right i)))))
         vec)))

(defn- mismatch-window [events idx window]
  (let [start (max 0 (- idx window))
        end (min (count events) (+ idx window 1))]
    (mapv (fn [i]
            {:idx i
             :event (event-view (nth events i))})
          (range start end))))

(defn- mismatch-window-by [view-fn events idx window]
  (let [start (max 0 (- idx window))
        end (min (count events) (+ idx window 1))]
    (mapv (fn [i]
            {:idx i
             :event (view-fn (nth events i))})
          (range start end))))

(defn- kind-counts [rows]
  (->> rows
       (map :kind)
       (remove nil?)
       frequencies
       (into (sorted-map))))

(defn- first-subseq-index [haystack needle]
  (let [n (count needle)
        h (count haystack)]
    (when (and (pos? n) (<= n h))
      (first
       (for [i (range (inc (- h n)))
             :when (= (mapv event-view (subvec haystack i (+ i n)))
                      (mapv event-view needle))]
         i)))))

(defn- count-mdata [^Expr root]
  (let [seen (java.util.IdentityHashMap.)]
    (letfn [(go [^Expr e]
                (cond
                  (nil? e) 0
                  (.containsKey seen e) 0
                  :else
                  (do
                    (.put seen e Boolean/TRUE)
                    (+ (if (= Expr/MDATA (.tag e)) 1 0)
                       (case (int (.tag e))
                         3 (+ (go (.o0 e)) (go (.o1 e)))
                         4 (+ (go (.o1 e)) (go (.o2 e)))
                         5 (+ (go (.o1 e)) (go (.o2 e)))
                         6 (+ (go (.o1 e)) (go (.o2 e)) (go (.o3 e)))
                         9 (go (.o1 e))
                         10 (go (.o1 e))
                         0)))))]
      (go root))))

(defn- trace-ansatz-ctx!
  [ctx decl-name out-path fuel]
  (let [env (:env ctx)
        resolve-fn (:resolve-fn ctx)
        rank (when-let [ranks (:decl-ranks ctx)]
               (.get ^java.util.HashMap ranks (ansatz-name/from-string decl-name)))
        _ (when rank
            (storage/skip-to! ctx rank))
        ^ConstantInfo ci (resolve-fn decl-name)]
    (when-not ci
      (throw (ex-info "Declaration not found" {:decl decl-name})))
    (with-open [w (FileWriter. out-path false)]
      (TypeChecker/checkConstantTraced env ci (long fuel) w))
    {:decl decl-name
     :out out-path
     :type-mdata (count-mdata (.type ci))
     :value-mdata (count-mdata (.value ci))
     :events (count (event-lines out-path))}))

(defn trace-ansatz!
  [store-path branch-name decl-name out-path fuel]
  (let [store (storage/open-store store-path)
        ctx (storage/prepare-verify store branch-name
                                    :log-file (str (System/getProperty "java.io.tmpdir")
                                                   "/ansatz-kernel-trace.log"))]
    (trace-ansatz-ctx! ctx decl-name out-path fuel)))

(defn- lake-bin? [lean-bin]
  (and lean-bin (= "lake" (.getName (io/file lean-bin)))))

(defn- lake-project-file? [lean-root]
  (or (.exists (io/file lean-root "lakefile.lean"))
      (.exists (io/file lean-root "lakefile.toml"))))

(defn- lake-project-file-mode? [lean-root lean-file lean-bin]
  (and (not (str/starts-with? lean-file "src/"))
       (not (lake-bin? lean-bin))
       (lake-project-file? lean-root)))

(defn- default-lean-bin []
  (let [instrumented (io/file (System/getProperty "user.dir")
                              "../lean4/build/release/stage1/bin/lean")
        elan-lean (io/file (System/getProperty "user.home") ".elan/bin/lean")]
    (cond
      (.exists instrumented) (.getCanonicalPath instrumented)
      (.exists elan-lean) (.getPath elan-lean)
      :else "lean")))

(defn- lake-lean-path [lean-root]
  (let [root-lib (io/file lean-root ".lake/build/lib/lean")
        packages-dir (io/file lean-root ".lake/packages")
        package-libs (if (.isDirectory packages-dir)
                       (keep (fn [pkg]
                               (let [lib (io/file pkg ".lake/build/lib/lean")]
                                 (when (.isDirectory lib) (.getPath lib))))
                             (.listFiles packages-dir))
                       [])]
    (->> (cons (.getPath root-lib) package-libs)
         (filter seq)
         (str/join java.io.File/pathSeparator))))

(defn- trace-lean-command [lean-root lean-file lean-bin]
  (if (lake-bin? lean-bin)
    [lean-bin "env" "lean" "-j1" lean-file]
    (if (lake-project-file-mode? lean-root lean-file lean-bin)
      [(or lean-bin (default-lean-bin)) "-j1" lean-file]
      [(or lean-bin (str lean-root "/build/release/stage1/bin/lean"))
       "-j1" "-R" "src" lean-file])))

(defn- lean-version-command [lean-root lean-file lean-bin]
  (if (lake-bin? lean-bin)
    [lean-bin "env" "lean" "--version"]
    [(first (trace-lean-command lean-root lean-file lean-bin)) "--version"]))

(defonce ^:private lean-version-cache (atom {}))

(defn- lean-version [lean-root lean-file lean-bin]
  (let [cmd (lean-version-command lean-root lean-file lean-bin)
        cache-key [lean-root cmd]]
    (or (get @lean-version-cache cache-key)
        (let [{:keys [exit out err]} (apply sh/sh (concat cmd [:dir lean-root]))
              version (if (zero? exit) (str/trim out) (str/trim err))]
          (swap! lean-version-cache assoc cache-key version)
          version))))

(defn- expected-lean-version [lean-root]
  (let [toolchain (io/file lean-root "lean-toolchain")]
    (when (.exists toolchain)
      (let [text (str/trim (slurp toolchain))]
        (or (second (re-find #"leanprover/lean4:v([^\s]+)" text))
            (second (re-find #"leanprover/lean4:([^\s]+)" text))
            text)))))

(defn- lean-version-compatible? [actual expected]
  (or (not (seq expected))
      (and (string? actual)
           (str/includes? actual expected))))

(defn- trace-lean-env [lean-root lean-file lean-bin decl-name out-path]
  (cond-> {"LEAN_KERNEL_TRACE" out-path}
    (seq decl-name)
    (assoc "LEAN_KERNEL_TRACE_DECL" decl-name)

    (lake-project-file-mode? lean-root lean-file lean-bin)
    (assoc "LEAN_PATH" (lake-lean-path lean-root))))

(defn trace-lean!
  ([lean-root lean-file decl-name out-path]
   (trace-lean! lean-root lean-file decl-name out-path nil))
  ([lean-root lean-file decl-name out-path lean-bin]
   (let [cmd (trace-lean-command lean-root lean-file lean-bin)
         version (lean-version lean-root lean-file lean-bin)
         expected-version (expected-lean-version lean-root)
         {:keys [exit out err]}
         (apply sh/sh
                (concat cmd
                        [:dir lean-root
                         :env (trace-lean-env lean-root lean-file lean-bin decl-name out-path)]))]
     (when (and (not (zero? exit))
                (not (.exists (io/file out-path))))
       (throw (ex-info "Lean trace command failed"
                       {:exit exit
                        :err err
                        :out out
                        :cmd cmd
                        :lean-root lean-root
                        :lean-file lean-file
                        :decl decl-name})))
     (when-not (.exists (io/file out-path))
       (throw (ex-info "Lean trace file was not produced"
                       {:cmd cmd
                        :lean-root lean-root
                        :lean-file lean-file
                        :decl decl-name
                        :out out-path
                        :hint "Check that the Lean binary is instrumented and the declaration filter matches."})))
     (let [analysis (trace-file-analysis out-path decl-name)]
       {:decl decl-name
        :out out-path
        :exit exit
        :err err
        :out-text out
        :version version
        :expected-version expected-version
        :version-compatible? (lean-version-compatible? version expected-version)
        :nonzero-exit? (not (zero? exit))
        :trace-analysis analysis
        :trace-ambiguous? (boolean (:ambiguous? analysis))
        :events (count (event-lines out-path decl-name))}))))

(defn- trace-lean-file!
  "Trace all kernel checks produced while elaborating lean-file once.
   Declaration-specific traces are sliced from this file by exact decl markers."
  [lean-root lean-file out-path lean-bin]
  (let [cmd (trace-lean-command lean-root lean-file lean-bin)
        version (lean-version lean-root lean-file lean-bin)
        expected-version (expected-lean-version lean-root)
        {:keys [exit out err]}
        (apply sh/sh
               (concat cmd
                       [:dir lean-root
                        :env (trace-lean-env lean-root lean-file lean-bin nil out-path)]))]
    (when (and (not (zero? exit))
               (not (.exists (io/file out-path))))
      (throw (ex-info "Lean grouped trace command failed"
                      {:exit exit
                       :err err
                       :out out
                       :cmd cmd
                       :lean-root lean-root
                       :lean-file lean-file})))
    (when-not (.exists (io/file out-path))
      (throw (ex-info "Lean grouped trace file was not produced"
                      {:cmd cmd
                       :lean-root lean-root
                       :lean-file lean-file
                       :out out-path
                       :hint "Check that the Lean binary is instrumented."})))
    {:out out-path
     :exit exit
     :err err
     :out-text out
     :version version
     :expected-version expected-version
     :version-compatible? (lean-version-compatible? version expected-version)
     :nonzero-exit? (not (zero? exit))}))

(defn- safe-decl-name [decl-name]
  (-> decl-name
      (str/replace "/" "_")
      (str/replace "?" "_qmark_")
      (str/replace #"[^A-Za-z0-9._-]" "_")))

(defn- write-lines! [path lines]
  (with-open [w (io/writer path)]
    (doseq [line lines]
      (.write w line)
      (.write w "\n"))))

(defn compare-traces
  ([left-path right-path]
   (compare-traces left-path right-path 10 2))
  ([left-path right-path max-mismatches window]
   (compare-traces left-path nil right-path nil max-mismatches window))
  ([left-path left-decl right-path right-decl max-mismatches window]
   (let [left (event-lines left-path left-decl)
         right (event-lines right-path right-decl)
         common (min (count left) (count right))
         mismatches (mismatch-indices left right)
         mismatch (first mismatches)]
     {:left {:path left-path
             :decl left-decl
             :events (count left)
             :by (by-histogram left)}
      :right {:path right-path
              :decl right-decl
              :events (count right)
              :by (by-histogram right)}
      :common-prefix
      (loop [i 0]
        (if (or (>= i common)
                (not= (event-view (nth left i))
                      (event-view (nth right i))))
          i
          (recur (inc i))))
      :mismatch-count (count mismatches)
      :mismatch-indices (vec (take max-mismatches mismatches))
      :first-mismatch
      (when mismatch
        {:idx mismatch
         :left (event-view (nth left mismatch))
         :right (event-view (nth right mismatch))
         :left-window (mismatch-window left mismatch window)
         :right-window (mismatch-window right mismatch window)})
      :length-mismatch
      (when (not= (count left) (count right))
        {:left (count left)
         :right (count right)})
      :alignment
      (let [anchor-len (min 5 (count right))
            anchor (subvec right 0 anchor-len)
            idx (first-subseq-index left anchor)]
        (when idx
          {:left-start idx
           :anchor-len anchor-len
           :right-prefix (mapv event-view anchor)
           :left-window (mismatch-window left idx 2)}))})))

(defn compare-traces-normalized-fvars
  ([left-path right-path]
   (compare-traces-normalized-fvars left-path nil right-path nil 10 2))
  ([left-path left-decl right-path right-decl max-mismatches window]
   (let [view-fn event-view-normalized-fvars
         left (event-lines left-path left-decl)
         right (event-lines right-path right-decl)
         common (min (count left) (count right))
         mismatches (mismatch-indices-by view-fn left right)
         mismatch (first mismatches)]
     {:left {:path left-path
             :decl left-decl
             :events (count left)
             :by (by-histogram left)}
      :right {:path right-path
              :decl right-decl
              :events (count right)
              :by (by-histogram right)}
      :common-prefix
      (loop [i 0]
        (if (or (>= i common)
                (not= (view-fn (nth left i))
                      (view-fn (nth right i))))
          i
          (recur (inc i))))
      :mismatch-count (count mismatches)
      :mismatch-indices (vec (take max-mismatches mismatches))
      :first-mismatch
      (when mismatch
        {:idx mismatch
         :left (view-fn (nth left mismatch))
         :right (view-fn (nth right mismatch))
         :left-window (mismatch-window-by view-fn left mismatch window)
         :right-window (mismatch-window-by view-fn right mismatch window)})
      :length-mismatch
      (when (not= (count left) (count right))
        {:left (count left)
         :right (count right)})})))

(defn- semantic-mismatches [left right view-fn]
  (let [left-count (count left)
        right-count (count right)]
    (loop [i 0
           j 0
           matched 0
           phase-compatible 0
           skipped-left []
           skipped-right []]
      (cond
        (and (>= i left-count) (>= j right-count))
        {:matched matched
         :matched-all? true
         :phase-compatible phase-compatible
         :skipped-left skipped-left
         :skipped-right skipped-right}

        (>= i left-count)
        (let [remaining (subvec right j right-count)]
          {:matched matched
           :matched-all? (every? #(semantic-epsilon? (view-fn %)) remaining)
           :phase-compatible phase-compatible
           :skipped-left skipped-left
           :skipped-right (into skipped-right
                                (map (fn [k] {:idx k :event (view-fn (nth right k))})
                                     (range j right-count)))
           :first-mismatch (when-not (every? #(semantic-epsilon? (view-fn %)) remaining)
                             {:left-idx i :right-idx j
                              :left nil
                              :right (view-fn (nth right j))})})

        (>= j right-count)
        (let [remaining (subvec left i left-count)]
          {:matched matched
           :matched-all? (every? #(semantic-epsilon? (view-fn %)) remaining)
           :phase-compatible phase-compatible
           :skipped-left (into skipped-left
                               (map (fn [k] {:idx k :event (view-fn (nth left k))})
                                    (range i left-count)))
           :skipped-right skipped-right
           :first-mismatch (when-not (every? #(semantic-epsilon? (view-fn %)) remaining)
                             {:left-idx i :right-idx j
                              :left (view-fn (nth left i))
                              :right nil})})

        :else
        (let [lv (view-fn (nth left i))
              rv (view-fn (nth right j))]
          (cond
            (compatible-view? lv rv)
            (recur (inc i) (inc j) (inc matched)
                   (+ phase-compatible (if (and (not= (:by lv) (:by rv))
                                                (phase-compatible-view? lv rv))
                                         1 0))
                   skipped-left skipped-right)

            (semantic-epsilon? lv)
            (recur (inc i) j matched phase-compatible
                   (conj skipped-left {:idx i :kind (semantic-epsilon-kind lv) :event lv})
                   skipped-right)

            (semantic-epsilon? rv)
            (recur i (inc j) matched phase-compatible
                   skipped-left
                   (conj skipped-right {:idx j :kind (semantic-epsilon-kind rv) :event rv}))

            :else
            {:matched matched
             :matched-all? false
             :phase-compatible phase-compatible
             :skipped-left skipped-left
             :skipped-right skipped-right
             :first-mismatch {:left-idx i
                              :right-idx j
                              :left lv
                              :right rv}}))))))

(defn compare-traces-semantic
  "Compare traces after normalizing fvars and treating successful reflexive
   quick checks as epsilon events. These checks are sensitive to pointer sharing:
   Lean may emit them where Ansatz has already short-circuited by identity."
  ([left-path right-path]
   (compare-traces-semantic left-path nil right-path nil 10 2))
  ([left-path left-decl right-path right-decl max-mismatches window]
   (let [view-fn event-view-normalized-fvars
         left (event-lines left-path left-decl)
         right (event-lines right-path right-decl)
         result (semantic-mismatches left right view-fn)
         first-mismatch (:first-mismatch result)
         left-idx (:left-idx first-mismatch)
         right-idx (:right-idx first-mismatch)
         skipped-left (:skipped-left result)
         skipped-right (:skipped-right result)]
     {:left {:path left-path
             :decl left-decl
             :events (count left)
             :by (by-histogram left)}
      :right {:path right-path
              :decl right-decl
              :events (count right)
              :by (by-histogram right)}
      :semantic {:matched (:matched result)
                 :matched-all? (:matched-all? result)
                 :phase-compatible (:phase-compatible result)
                 :skipped-left (count skipped-left)
                 :skipped-right (count skipped-right)
                 :skipped-left-by-kind (kind-counts skipped-left)
                 :skipped-right-by-kind (kind-counts skipped-right)
                 :skipped-left-window (vec (take max-mismatches skipped-left))
                 :skipped-right-window (vec (take max-mismatches skipped-right))}
      :first-mismatch
      (when first-mismatch
        (cond-> first-mismatch
          (some? left-idx) (assoc :left-window (mismatch-window-by view-fn left left-idx window))
          (some? right-idx) (assoc :right-window (mismatch-window-by view-fn right right-idx window))))
      :length-mismatch
      (when (not= (count left) (count right))
        {:left (count left)
         :right (count right)})})))

(defn- trace-mathlib-with-ctx!
  [ctx decl-name lean-root lean-file out-dir fuel lean-bin]
  (let [safe-decl (safe-decl-name decl-name)
        ansatz-out (str out-dir "/" safe-decl ".ansatz.jsonl")
        lean-out (str out-dir "/" safe-decl ".lean.jsonl")]
    (.mkdirs (io/file out-dir))
    {:ansatz (trace-ansatz-ctx! ctx decl-name ansatz-out fuel)
     :lean (trace-lean! lean-root lean-file decl-name lean-out lean-bin)
     :compare (compare-traces lean-out decl-name ansatz-out nil 10 2)
     :semantic (compare-traces-semantic lean-out decl-name ansatz-out nil 10 2)}))

(defn- sliced-lean-result [decl-name lean-file lean-out shared-lean-result]
  (let [analysis (trace-file-analysis lean-out decl-name)]
    (assoc shared-lean-result
           :decl decl-name
           :lean-file lean-file
           :out lean-out
           :trace-analysis analysis
           :trace-ambiguous? (boolean (:ambiguous? analysis))
           :events (count (event-lines lean-out decl-name)))))

(defn- trace-mathlib-with-sliced-lean!
  [ctx decl-name lean-file lean-out shared-lean-result out-dir fuel]
  (let [safe-decl (safe-decl-name decl-name)
        ansatz-out (str out-dir "/" safe-decl ".ansatz.jsonl")
        lean-result (sliced-lean-result decl-name lean-file lean-out shared-lean-result)]
    {:ansatz (trace-ansatz-ctx! ctx decl-name ansatz-out fuel)
     :lean lean-result
     :compare (compare-traces lean-out decl-name ansatz-out nil 10 2)
     :semantic (compare-traces-semantic lean-out decl-name ansatz-out nil 10 2)}))

(defn- annotate-row-result [decl file result]
  (let [lean-events (long (or (get-in result [:lean :events]) 0))
        ansatz-events (long (or (get-in result [:ansatz :events]) 0))
        trace-comparable? (and (pos? lean-events) (pos? ansatz-events))
        semantic-ok? (and trace-comparable?
                          (true? (get-in result [:semantic :semantic :matched-all?])))
        raw-length-ok? (and trace-comparable?
                            (nil? (get-in result [:compare :length-mismatch])))
        lean-exit-ok? (not (true? (get-in result [:lean :nonzero-exit?])))
        lean-trace-ambiguous? (true? (get-in result [:lean :trace-ambiguous?]))
        source-mdata-mismatch? (and trace-comparable?
                                    (source-mdata-mismatch? result semantic-ok?))]
    (assoc result
           :decl decl
           :lean-file file
           :trace-comparable? trace-comparable?
           :lean-exit-ok? lean-exit-ok?
           :lean-trace-ambiguous? lean-trace-ambiguous?
           :semantic-ok? semantic-ok?
           :raw-length-ok? raw-length-ok?
           :source-mdata-mismatch? source-mdata-mismatch?)))

(defn trace-mathlib!
  ([store-path branch-name decl-name lean-root lean-file out-dir]
   (trace-mathlib! store-path branch-name decl-name lean-root lean-file out-dir
                   100000000 nil))
  ([store-path branch-name decl-name lean-root lean-file out-dir fuel lean-bin]
   (let [store (storage/open-store store-path)
         ctx (storage/prepare-verify store branch-name
                                     :log-file (str (System/getProperty "java.io.tmpdir")
                                                    "/ansatz-kernel-trace.log"))]
     (trace-mathlib-with-ctx! ctx decl-name lean-root lean-file out-dir fuel lean-bin))))

(defn- read-batch-manifest [manifest-path]
  (with-open [r (io/reader manifest-path)]
    (->> (line-seq r)
         (keep (fn [line]
                 (let [line (str/trim line)]
                   (when (and (seq line) (not (str/starts-with? line "#")))
                     (let [[decl file] (str/split line #"\s+" 2)]
                       (when-not (and (seq decl) (seq file))
                         (throw (ex-info "Invalid trace manifest row"
                                         {:line line :manifest manifest-path})))
                       {:decl decl :file file})))))
         doall)))

(defn- batch-result [results]
  (let [total (count results)
        trace-comparable (count (filter :trace-comparable? results))
        semantic-ok (count (filter :semantic-ok? results))
        raw-length-ok (count (filter :raw-length-ok? results))
        lean-exit-ok (count (filter :lean-exit-ok? results))
        source-mdata-mismatch (count (filter :source-mdata-mismatch? results))
        ambiguous-lean-trace (count (filter :lean-trace-ambiguous? results))
        grouped-fallback (count (filter :grouped-fallback? results))
        errors (count (filter :error results))]
    {:total total
     :trace-comparable trace-comparable
     :raw-length-ok raw-length-ok
     :semantic-ok semantic-ok
     :lean-exit-ok lean-exit-ok
     :source-mdata-mismatch source-mdata-mismatch
     :ambiguous-lean-trace ambiguous-lean-trace
     :grouped-fallback grouped-fallback
     :errors errors
     :results results}))

(defn- error-row-result [decl file ex]
  {:decl decl
   :lean-file file
   :error (str (.getClass ex) ": " (.getMessage ex))
   :trace-comparable? false
   :semantic-ok? false
   :raw-length-ok? false
   :lean-trace-ambiguous? false
   :source-mdata-mismatch? false})

(defn trace-batch!
  "Trace a manifest of declarations. Manifest rows are:
     <decl-name> <lean-file-relative-to-lean-root>
   Blank lines and # comments are ignored."
  ([store-path branch-name lean-root manifest-path out-dir]
   (trace-batch! store-path branch-name lean-root manifest-path out-dir 100000000 nil))
  ([store-path branch-name lean-root manifest-path out-dir fuel lean-bin]
   (let [rows (read-batch-manifest manifest-path)
         store (storage/open-store store-path)
         ctx (storage/prepare-verify store branch-name
                                     :log-file (str (System/getProperty "java.io.tmpdir")
                                                    "/ansatz-kernel-trace.log"))
         results
         (mapv
          (fn [{:keys [decl file]}]
            (try
              (annotate-row-result
               decl file
               (trace-mathlib-with-ctx! ctx decl lean-root file out-dir fuel lean-bin))
              (catch Throwable ex
                (error-row-result decl file ex))))
          rows)]
     (batch-result results))))

(defn- write-sliced-trace!
  [raw-lines parsed-lines decl out-path]
  (write-lines! out-path (slice-decl-raw-lines raw-lines parsed-lines decl)))

(defn trace-batch-grouped!
  "Trace a manifest using one Lean process per source file.
   The shared Lean trace is sliced by exact declaration markers before comparison."
  ([store-path branch-name lean-root manifest-path out-dir]
   (trace-batch-grouped! store-path branch-name lean-root manifest-path out-dir 100000000 nil))
  ([store-path branch-name lean-root manifest-path out-dir fuel lean-bin]
   (let [rows (vec (read-batch-manifest manifest-path))
         store (storage/open-store store-path)
         ctx (storage/prepare-verify store branch-name
                                     :log-file (str (System/getProperty "java.io.tmpdir")
                                                    "/ansatz-kernel-trace.log"))
         out-dir-file (io/file out-dir)
         _ (.mkdirs out-dir-file)
         grouped (group-by :file rows)
         result-by-row (atom {})]
     (doseq [[file file-rows] grouped]
       (let [safe-file (safe-decl-name file)
             shared-lean-out (str out-dir "/" safe-file ".lean.all.jsonl")]
         (try
           (let [shared-lean-result (trace-lean-file! lean-root file shared-lean-out lean-bin)
                 raw-lines (read-raw-lines shared-lean-out)
                 parsed-lines (mapv #(json/read-str % :key-fn keyword) raw-lines)]
             (doseq [{:keys [decl] :as row} file-rows]
               (let [safe-decl (safe-decl-name decl)
                     lean-out (str out-dir "/" safe-decl ".lean.jsonl")]
                 (try
                   (write-sliced-trace! raw-lines parsed-lines decl lean-out)
                   (swap! result-by-row assoc row
                          (annotate-row-result
                           decl file
                           (trace-mathlib-with-sliced-lean!
                            ctx decl file lean-out shared-lean-result out-dir fuel)))
                   (catch Throwable ex
                     (swap! result-by-row assoc row
                            {:decl decl
                             :lean-file file
                             :error (str (.getClass ex) ": " (.getMessage ex))
                             :trace-comparable? false
                             :semantic-ok? false
                             :raw-length-ok? false
                             :lean-trace-ambiguous? false
                             :source-mdata-mismatch? false}))))))
           (catch Throwable ex
             ;; The Lean trace writer can interleave full-file JSON events on
             ;; some large Mathlib files even under -j1. Keep grouped mode fast
             ;; for normal files, but fall back to the original per-declaration
             ;; filtered Lean trace when the shared file cannot be parsed.
             (doseq [{:keys [decl] :as row} file-rows]
               (swap! result-by-row assoc row
                      (try
                        (assoc
                         (annotate-row-result
                          decl file
                          (trace-mathlib-with-ctx!
                           ctx decl lean-root file out-dir fuel lean-bin))
                         :grouped-fallback? true
                         :grouped-fallback-cause (str (.getClass ex) ": " (.getMessage ex)))
                        (catch Throwable fallback-ex
                          (assoc (error-row-result decl file fallback-ex)
                                 :grouped-fallback? true
                                 :grouped-fallback-cause (str (.getClass ex) ": "
                                                              (.getMessage ex)))))))))))
     (batch-result (mapv @result-by-row rows)))))

(defn summarize-batch-result
  ([result]
   (summarize-batch-result result {}))
  ([result {:keys [strict-lean-exit?]
            :or {strict-lean-exit? false}
            :as opts}]
   (let [rows (:results result)
         strict-lean-version? (boolean (:strict-lean-version? opts))
         compact-text (fn [x]
                        (let [text (str/replace (str x) #"\s+" " ")]
                          (subs text 0 (min 1000 (count text)))))
         lean-nonzero? (fn [row]
                         (and (:trace-comparable? row)
                              (false? (:lean-exit-ok? row))))
         lean-version-mismatch? (fn [row]
                                  (and (get-in row [:lean :expected-version])
                                       (false? (get-in row [:lean :version-compatible?]))))
         bad? (fn [row]
                (or (:error row)
                    (not (:trace-comparable? row))
                    (:lean-trace-ambiguous? row)
                    (not (:semantic-ok? row))
                    (:source-mdata-mismatch? row)
                    (and strict-lean-exit?
                         (lean-nonzero? row))
                    (and strict-lean-version?
                         (lean-version-mismatch? row))))
         event-count (fn [row side]
                       (long (or (get-in row [side :events]) 0)))
         skipped-count (fn [row side]
                         (long (or (get-in row [:semantic :semantic side]) 0)))
         skipped-kind-counts (fn [side]
                               (->> rows
                                    (map #(get-in % [:semantic :semantic side]))
                                    (remove nil?)
                                    (apply merge-with +)
                                    (into (sorted-map))))
         phase-compatible-count (fn [row]
                                  (long (or (get-in row [:semantic :semantic :phase-compatible]) 0)))
         length-drift? (fn [row]
                         (and (:trace-comparable? row)
                              (not (:raw-length-ok? row))))
         length-row (fn [row]
                      (let [lean-events (event-count row :lean)
                            ansatz-events (event-count row :ansatz)]
                        {:decl (:decl row)
                         :file (:lean-file row)
                         :lean-events lean-events
                         :ansatz-events ansatz-events
                         :delta (- ansatz-events lean-events)
                         :skipped-left (skipped-count row :skipped-left)
                         :skipped-right (skipped-count row :skipped-right)}))
         row-summary (fn [row]
                       (cond-> {:decl (:decl row)
                                :file (:lean-file row)
                                :trace-comparable? (boolean (:trace-comparable? row))
                                :semantic-ok? (boolean (:semantic-ok? row))
                                :raw-length-ok? (boolean (:raw-length-ok? row))
                                :lean-exit-ok? (boolean (:lean-exit-ok? row))
                                :lean-trace-ambiguous? (boolean (:lean-trace-ambiguous? row))
                                :source-mdata-mismatch? (boolean (:source-mdata-mismatch? row))}
                         (:error row) (assoc :error (:error row))
                         (some? (get-in row [:lean :exit])) (assoc :lean-exit (get-in row [:lean :exit]))
                         (seq (get-in row [:lean :err])) (assoc :lean-stderr (compact-text (get-in row [:lean :err])))
                         (seq (get-in row [:lean :version])) (assoc :lean-version (get-in row [:lean :version]))
                         (seq (get-in row [:lean :expected-version])) (assoc :expected-lean-version (get-in row [:lean :expected-version]))
                         (some? (get-in row [:lean :version-compatible?])) (assoc :lean-version-compatible? (boolean (get-in row [:lean :version-compatible?])))
                         (get-in row [:lean :events]) (assoc :lean-events (get-in row [:lean :events]))
                         (and (:lean-trace-ambiguous? row)
                              (get-in row [:lean :trace-analysis]))
                         (assoc :lean-trace-analysis (get-in row [:lean :trace-analysis]))
                         (get-in row [:ansatz :events]) (assoc :ansatz-events (get-in row [:ansatz :events]))
                         (get-in row [:semantic :first-mismatch])
                         (assoc :first-mismatch (get-in row [:semantic :first-mismatch]))))]
     (-> result
         (dissoc :results)
         (assoc :semantic-with-epsilon-skips (- (long (:semantic-ok result))
                                                (long (:raw-length-ok result)))
               ;; Kept for compatibility with older reports; this now includes
               ;; all narrow semantic epsilon skips, not just reflexive quicks.
                :semantic-with-reflexive-skips (- (long (:semantic-ok result))
                                                  (long (:raw-length-ok result)))
                :lean-nonzero-exit (count (filter lean-nonzero? rows))
                :ambiguous-lean-trace (count (filter :lean-trace-ambiguous? rows))
                :length-drift (count (filter length-drift? rows))
                :lean-events (reduce + (map #(event-count % :lean) rows))
                :ansatz-events (reduce + (map #(event-count % :ansatz) rows))
                :net-event-delta (reduce + (map #(- (event-count % :ansatz)
                                                    (event-count % :lean))
                                                rows))
                :semantic-phase-compatible (reduce + (map phase-compatible-count rows))
                :semantic-skipped-left (reduce + (map #(skipped-count % :skipped-left) rows))
                :semantic-skipped-right (reduce + (map #(skipped-count % :skipped-right) rows))
                :semantic-skipped-left-by-kind (skipped-kind-counts :skipped-left-by-kind)
                :semantic-skipped-right-by-kind (skipped-kind-counts :skipped-right-by-kind)
                :strict-lean-exit? strict-lean-exit?
                :strict-lean-version? strict-lean-version?
                :lean-version-mismatch (count (filter lean-version-mismatch? rows))
                :largest-length-deltas (->> rows
                                            (filter length-drift?)
                                            (map length-row)
                                            (sort-by #(Math/abs (long (:delta %))) >)
                                            (take 10)
                                            vec)
                :lean-nonzero-results (mapv row-summary (filter lean-nonzero? rows))
                :lean-version-mismatch-results (mapv row-summary (filter lean-version-mismatch? rows))
                :bad-results (mapv row-summary (filter bad? rows))
                :strict-ok? (empty? (filter bad? rows)))))))

(defn- row-event-count [row side]
  (long (or (get-in row [side :events]) 0)))

(defn- row-skipped-count [row side]
  (long (or (get-in row [:semantic :semantic side]) 0)))

(defn- row-delta [row]
  (- (row-event-count row :ansatz)
     (row-event-count row :lean)))

(defn- row-promotable? [row]
  (and (not (:error row))
       (:trace-comparable? row)
       (not (:lean-trace-ambiguous? row))
       (:semantic-ok? row)
       (not (:source-mdata-mismatch? row))))

(defn- row-reasons [row]
  (cond-> []
    (:error row)
    (conj :error)

    (and (not (:error row))
         (zero? (row-event-count row :lean)))
    (conj :lean-zero-events)

    (and (not (:error row))
         (zero? (row-event-count row :ansatz)))
    (conj :ansatz-zero-events)

    (and (not (:error row))
         (not (:trace-comparable? row)))
    (conj :not-trace-comparable)

    (:lean-trace-ambiguous? row)
    (conj :ambiguous-lean-trace)

    (:source-mdata-mismatch? row)
    (conj :source-mdata-mismatch)

    (and (:trace-comparable? row)
         (not (:semantic-ok? row))
         (not (:source-mdata-mismatch? row))
         (not (:lean-trace-ambiguous? row)))
    (conj :semantic-mismatch)))

(defn- row-warnings [row]
  (cond-> []
    (and (get-in row [:lean :expected-version])
         (false? (get-in row [:lean :version-compatible?])))
    (conj :lean-version-mismatch)

    (and (:trace-comparable? row)
         (false? (:lean-exit-ok? row)))
    (conj :lean-nonzero-exit)

    (and (:trace-comparable? row)
         (not (:raw-length-ok? row)))
    (conj :raw-length-drift)))

(defn- compact-detail [row]
  (let [detail (or (:error row)
                   (when (:lean-trace-ambiguous? row)
                     (get-in row [:lean :trace-analysis]))
                   (get-in row [:semantic :first-mismatch])
                   (get-in row [:compare :first-mismatch])
                   (get-in row [:compare :length-mismatch])
                   (get-in row [:lean :err])
                   "")
        text (str/replace (pr-str detail) #"\s+" " ")]
    (subs text 0 (min 2000 (count text)))))

(defn- tsv-field [x]
  (-> (if (nil? x) "" (str x))
      (str/replace #"\t" " ")
      (str/replace #"\r?\n" " ")))

(defn- keyword-list-field [xs]
  (->> xs (map name) (str/join ",")))

(defn- manifest-line [row]
  (str (:decl row) "\t" (:lean-file row)))

(defn- quarantine-line [row]
  (str/join "\t"
            (map tsv-field
                 [(:decl row)
                  (:lean-file row)
                  (keyword-list-field (row-reasons row))
                  (keyword-list-field (row-warnings row))
                  (row-event-count row :lean)
                  (row-event-count row :ansatz)
                  (row-delta row)
                  (row-skipped-count row :skipped-left)
                  (row-skipped-count row :skipped-right)
                  (compact-detail row)])))

(defn- frequencies-by-keywords [f rows]
  (->> rows
       (mapcat f)
       frequencies
       (into (sorted-map))))

(defn write-curation-files!
  "Write promote.tsv, quarantine.tsv, and summary.edn for a traced candidate batch.
   Promotion is intentionally semantic: raw length drift and Lean nonzero exit are
   warnings when both traces are comparable and semantically aligned."
  [result report-dir]
  (let [rows (:results result)
        promoted (filter row-promotable? rows)
        quarantined (remove row-promotable? rows)
        report-dir-file (io/file report-dir)
        promote-path (.getPath (io/file report-dir-file "promote.tsv"))
        quarantine-path (.getPath (io/file report-dir-file "quarantine.tsv"))
        summary-path (.getPath (io/file report-dir-file "summary.edn"))
        batch-summary (summarize-batch-result result)
        summary (assoc (dissoc batch-summary :bad-results)
                       :bad-results (count (:bad-results batch-summary))
                       :promoted (count promoted)
                       :quarantined (count quarantined)
                       :promoted-with-warnings (count (filter #(seq (row-warnings %)) promoted))
                       :quarantine-by-reason (frequencies-by-keywords row-reasons quarantined)
                       :warnings-by-kind (frequencies-by-keywords row-warnings rows)
                       :report-files {:promote promote-path
                                      :quarantine quarantine-path
                                      :summary summary-path})]
    (.mkdirs report-dir-file)
    (write-lines! promote-path
                  (concat ["# Promotable kernel trace declarations."
                           "# Generated by ansatz.tools.kernel-trace curate-batch."
                           "# Format: <declaration>\t<lean-file-relative-to-lean-root>"]
                          (map manifest-line promoted)))
    (write-lines! quarantine-path
                  (concat ["# Kernel trace declarations that need investigation before promotion."
                           "# Columns: decl\tfile\treasons\twarnings\tlean-events\tansatz-events\tdelta\tskipped-left\tskipped-right\tdetail"]
                          (map quarantine-line quarantined)))
    (with-open [w (io/writer summary-path)]
      (binding [*out* w]
        (prn summary)))
    summary))

(defn curate-batch!
  ([store-path branch-name lean-root manifest-path trace-out-dir report-dir]
   (curate-batch! store-path branch-name lean-root manifest-path trace-out-dir report-dir
                  100000000 nil))
  ([store-path branch-name lean-root manifest-path trace-out-dir report-dir fuel lean-bin]
   (write-curation-files!
    (trace-batch! store-path branch-name lean-root manifest-path trace-out-dir fuel lean-bin)
    report-dir)))

(defn curate-batch-grouped!
  ([store-path branch-name lean-root manifest-path trace-out-dir report-dir]
   (curate-batch-grouped! store-path branch-name lean-root manifest-path trace-out-dir report-dir
                          100000000 nil))
  ([store-path branch-name lean-root manifest-path trace-out-dir report-dir fuel lean-bin]
   (write-curation-files!
    (trace-batch-grouped! store-path branch-name lean-root manifest-path trace-out-dir fuel lean-bin)
    report-dir)))

(defn- run-main [args]
  (case (first args)
    "trace-ansatz"
    (let [[_ store branch decl out fuel] args
          fuel (Long/parseLong (or fuel "100000000"))]
      (prn (trace-ansatz! store branch decl out fuel)))

    "trace-lean"
    (let [[_ lean-root lean-file decl out lean-bin] args]
      (prn (trace-lean! lean-root lean-file decl out lean-bin)))

    "trace-mathlib"
    (let [[_ store branch decl lean-root lean-file out-dir fuel lean-bin] args
          fuel (Long/parseLong (or fuel "100000000"))]
      (prn (trace-mathlib! store branch decl lean-root lean-file out-dir fuel lean-bin)))

    "trace-batch"
    (let [[_ store branch lean-root manifest out-dir fuel lean-bin] args
          fuel (Long/parseLong (or fuel "100000000"))]
      (prn (trace-batch! store branch lean-root manifest out-dir fuel lean-bin)))

    "trace-batch-summary"
    (let [[_ store branch lean-root manifest out-dir fuel lean-bin] args
          fuel (Long/parseLong (or fuel "100000000"))]
      (prn (summarize-batch-result
            (trace-batch! store branch lean-root manifest out-dir fuel lean-bin))))

    "trace-batch-summary-strict"
    (let [[_ store branch lean-root manifest out-dir fuel lean-bin] args
          fuel (Long/parseLong (or fuel "100000000"))
          summary (summarize-batch-result
                   (trace-batch! store branch lean-root manifest out-dir fuel lean-bin)
                   {:strict-lean-exit? true
                    :strict-lean-version? true})]
      (prn summary)
      (when-not (:strict-ok? summary)
        (throw (ex-info "Strict trace batch summary failed"
                        (select-keys summary [:total
                                              :trace-comparable
                                              :semantic-ok
                                              :lean-nonzero-exit
                                              :lean-version-mismatch
                                              :errors
                                              :bad-results])))))

    "curate-batch"
    (let [[_ store branch lean-root manifest trace-out-dir report-dir fuel lean-bin] args
          fuel (Long/parseLong (or fuel "100000000"))]
      (prn (curate-batch! store branch lean-root manifest trace-out-dir report-dir fuel lean-bin)))

    "curate-batch-grouped"
    (let [[_ store branch lean-root manifest trace-out-dir report-dir fuel lean-bin] args
          fuel (Long/parseLong (or fuel "100000000"))]
      (prn (curate-batch-grouped! store branch lean-root manifest trace-out-dir report-dir fuel lean-bin)))

    "compare"
    (let [[_ left right max-mismatches window] args
          max-mismatches (Long/parseLong (or max-mismatches "10"))
          window (Long/parseLong (or window "2"))]
      (prn (compare-traces left right max-mismatches window)))

    "compare-normalized-fvars"
    (let [[_ left right max-mismatches window] args
          max-mismatches (Long/parseLong (or max-mismatches "10"))
          window (Long/parseLong (or window "2"))]
      (prn (compare-traces-normalized-fvars left nil right nil max-mismatches window)))

    "compare-semantic"
    (let [[_ left right max-mismatches window] args
          max-mismatches (Long/parseLong (or max-mismatches "10"))
          window (Long/parseLong (or window "2"))]
      (prn (compare-traces-semantic left nil right nil max-mismatches window)))

    (usage)))

(defn -main [& args]
  (let [exit-code (try
                    (run-main args)
                    0
                    (catch clojure.lang.ExceptionInfo ex
                      (binding [*out* *err*]
                        (println (.getMessage ex))
                        (when-let [data (ex-data ex)]
                          (prn data)))
                      1)
                    (catch Throwable ex
                      (.printStackTrace ex)
                      1))]
    (flush)
    (shutdown-agents)
    (System/exit exit-code)))
