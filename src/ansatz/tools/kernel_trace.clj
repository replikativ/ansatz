(ns ansatz.tools.kernel-trace
  "Helpers for tracing kernel checks and comparing trace streams."
  (:require [ansatz.export.storage :as storage]
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
  (println "  clojure -M -m ansatz.tools.kernel-trace compare <left> <right> [max-mismatches] [window]")
  (println "  clojure -M -m ansatz.tools.kernel-trace compare-normalized-fvars <left> <right> [max-mismatches] [window]")
  (println "  clojure -M -m ansatz.tools.kernel-trace compare-semantic <left> <right> [max-mismatches] [window]"))

(defn- read-json-lines [path]
  (with-open [r (io/reader path)]
    (doall
     (map #(json/read-str % :key-fn keyword)
          (line-seq r)))))

(defn- slice-decl-lines [lines decl-name]
  (let [decl-idxs (keep-indexed (fn [i x] (when (:decl x) i)) lines)]
    (if (and decl-name (seq decl-idxs))
      (if-let [start (first (filter #(= decl-name (:decl (nth lines %))) decl-idxs))]
        (let [end (or (first (filter #(< start %) decl-idxs))
                      (count lines))]
          (subvec (vec lines) start end))
        [])
      lines)))

(defn- event-lines
  ([path]
   (event-lines path nil))
  ([path decl-name]
   (-> (read-json-lines path)
       vec
       (slice-decl-lines decl-name)
       (->> (filter :by)
            vec))))

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

(defn- compatible-view? [a b]
  (and (= (:d a) (:d b))
       (= (:res a) (:res b))
       (= (:by a) (:by b))
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

(defn- trace-lean-env [lean-root lean-file lean-bin decl-name out-path]
  (cond-> {"LEAN_KERNEL_TRACE" out-path
           "LEAN_KERNEL_TRACE_DECL" decl-name}
    (lake-project-file-mode? lean-root lean-file lean-bin)
    (assoc "LEAN_PATH" (lake-lean-path lean-root))))

(defn trace-lean!
  ([lean-root lean-file decl-name out-path]
   (trace-lean! lean-root lean-file decl-name out-path nil))
  ([lean-root lean-file decl-name out-path lean-bin]
   (let [cmd (trace-lean-command lean-root lean-file lean-bin)
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
     {:decl decl-name
      :out out-path
      :exit exit
      :err err
      :out-text out
      :nonzero-exit? (not (zero? exit))
      :events (count (event-lines out-path decl-name))})))

(defn- safe-decl-name [decl-name]
  (-> decl-name
      (str/replace "/" "_")
      (str/replace "?" "_qmark_")
      (str/replace #"[^A-Za-z0-9._-]" "_")))

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
           skipped-left []
           skipped-right []]
      (cond
        (and (>= i left-count) (>= j right-count))
        {:matched matched
         :matched-all? true
         :skipped-left skipped-left
         :skipped-right skipped-right}

        (>= i left-count)
        (let [remaining (subvec right j right-count)]
          {:matched matched
           :matched-all? (every? #(reflexive-quick? (view-fn %)) remaining)
           :skipped-left skipped-left
           :skipped-right (into skipped-right
                                (map (fn [k] {:idx k :event (view-fn (nth right k))})
                                     (range j right-count)))
           :first-mismatch (when-not (every? #(reflexive-quick? (view-fn %)) remaining)
                             {:left-idx i :right-idx j
                              :left nil
                              :right (view-fn (nth right j))})})

        (>= j right-count)
        (let [remaining (subvec left i left-count)]
          {:matched matched
           :matched-all? (every? #(reflexive-quick? (view-fn %)) remaining)
           :skipped-left (into skipped-left
                               (map (fn [k] {:idx k :event (view-fn (nth left k))})
                                    (range i left-count)))
           :skipped-right skipped-right
           :first-mismatch (when-not (every? #(reflexive-quick? (view-fn %)) remaining)
                             {:left-idx i :right-idx j
                              :left (view-fn (nth left i))
                              :right nil})})

        :else
        (let [lv (view-fn (nth left i))
              rv (view-fn (nth right j))]
          (cond
            (compatible-view? lv rv)
            (recur (inc i) (inc j) (inc matched) skipped-left skipped-right)

            (reflexive-quick? lv)
            (recur (inc i) j matched
                   (conj skipped-left {:idx i :event lv})
                   skipped-right)

            (reflexive-quick? rv)
            (recur i (inc j) matched
                   skipped-left
                   (conj skipped-right {:idx j :event rv}))

            :else
            {:matched matched
             :matched-all? false
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
                 :skipped-left (count skipped-left)
                 :skipped-right (count skipped-right)
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
              (let [result (trace-mathlib-with-ctx! ctx decl lean-root file out-dir fuel lean-bin)
                    lean-events (long (or (get-in result [:lean :events]) 0))
                    ansatz-events (long (or (get-in result [:ansatz :events]) 0))
                    trace-comparable? (and (pos? lean-events) (pos? ansatz-events))
                    semantic-ok? (and trace-comparable?
                                      (true? (get-in result [:semantic :semantic :matched-all?])))
                    raw-length-ok? (and trace-comparable?
                                        (nil? (get-in result [:compare :length-mismatch])))
                    lean-exit-ok? (not (true? (get-in result [:lean :nonzero-exit?])))
                    source-mdata-mismatch? (and trace-comparable?
                                                (source-mdata-mismatch? result semantic-ok?))]
                (assoc result
                       :decl decl
                       :lean-file file
                       :trace-comparable? trace-comparable?
                       :lean-exit-ok? lean-exit-ok?
                       :semantic-ok? semantic-ok?
                       :raw-length-ok? raw-length-ok?
                       :source-mdata-mismatch? source-mdata-mismatch?))
              (catch Throwable ex
                {:decl decl
                 :lean-file file
                 :error (str (.getClass ex) ": " (.getMessage ex))
                 :trace-comparable? false
                 :semantic-ok? false
                 :raw-length-ok? false
                 :source-mdata-mismatch? false})))
          rows)
         total (count results)
         trace-comparable (count (filter :trace-comparable? results))
         semantic-ok (count (filter :semantic-ok? results))
         raw-length-ok (count (filter :raw-length-ok? results))
         lean-exit-ok (count (filter :lean-exit-ok? results))
         source-mdata-mismatch (count (filter :source-mdata-mismatch? results))
         errors (count (filter :error results))]
     {:total total
      :trace-comparable trace-comparable
      :raw-length-ok raw-length-ok
      :semantic-ok semantic-ok
      :lean-exit-ok lean-exit-ok
      :source-mdata-mismatch source-mdata-mismatch
      :errors errors
      :results results})))

(defn summarize-batch-result [result]
  (let [rows (:results result)
        bad? (fn [row]
               (or (:error row)
                   (not (:trace-comparable? row))
                   (not (:semantic-ok? row))
                   (:source-mdata-mismatch? row)))
        lean-nonzero? (fn [row]
                        (and (:trace-comparable? row)
                             (false? (:lean-exit-ok? row))))
        event-count (fn [row side]
                      (long (or (get-in row [side :events]) 0)))
        skipped-count (fn [row side]
                        (long (or (get-in row [:semantic :semantic side]) 0)))
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
                               :source-mdata-mismatch? (boolean (:source-mdata-mismatch? row))}
                        (:error row) (assoc :error (:error row))
                        (get-in row [:lean :events]) (assoc :lean-events (get-in row [:lean :events]))
                        (get-in row [:ansatz :events]) (assoc :ansatz-events (get-in row [:ansatz :events]))
                        (get-in row [:semantic :first-mismatch])
                        (assoc :first-mismatch (get-in row [:semantic :first-mismatch]))))]
    (-> result
        (dissoc :results)
        (assoc :semantic-with-reflexive-skips (- (long (:semantic-ok result))
                                                 (long (:raw-length-ok result)))
               :lean-nonzero-exit (count (filter lean-nonzero? rows))
               :length-drift (count (filter length-drift? rows))
               :lean-events (reduce + (map #(event-count % :lean) rows))
               :ansatz-events (reduce + (map #(event-count % :ansatz) rows))
               :net-event-delta (reduce + (map #(- (event-count % :ansatz)
                                                    (event-count % :lean))
                                                rows))
               :semantic-skipped-left (reduce + (map #(skipped-count % :skipped-left) rows))
               :semantic-skipped-right (reduce + (map #(skipped-count % :skipped-right) rows))
               :largest-length-deltas (->> rows
                                           (filter length-drift?)
                                           (map length-row)
                                           (sort-by #(Math/abs (long (:delta %))) >)
                                           (take 10)
                                           vec)
               :bad-results (mapv row-summary (filter bad? rows))))))

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
                    (catch Throwable ex
                      (.printStackTrace ex)
                      1))]
    (flush)
    (shutdown-agents)
    (System/exit exit-code)))
