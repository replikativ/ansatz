(ns build-audit
  "Read source as data; never load optional namespaces while auditing packaging."
  (:require [clojure.java.io :as io]))

(def pattern-profile
  {:schema "lean-compiler-dependency/1" :lib 'org.replikativ/pattern :mvn/version "1.0.452"
   :source-git/url "https://github.com/replikativ/pattern.git"
   :source-git/sha "6d0242ee589d88b336f7dd6f820efa993d2b6f3b" :prototype-aot false})

(defn- fail! [message data] (throw (ex-info message data)))
(defn verify-dependency! [deps]
  (when-not (and (= #{'org.replikativ/ansatz 'org.replikativ/pattern} (set (keys (:deps deps))))
                 (= {:mvn/version (:mvn/version pattern-profile)} (get-in deps [:deps 'org.replikativ/pattern]))
                 (= {:git/url (:source-git/url pattern-profile) :git/sha (:source-git/sha pattern-profile)}
                    (get-in deps [:aliases :pattern-git :override-deps 'org.replikativ/pattern])))
    (fail! "Module dependencies drift from the compiler inventory" {}))
  true)
(defn- resolver-symbol? [x] (and (symbol? x) (= "requiring-resolve" (name x))))
(defn- reader-aliases! [reader-ns form]
  ;; Auto-resolved keywords need alias names while reading later forms. Alias
  ;; every declared name to the scratch reader namespace; keyword values are
  ;; inert to this audit. Never require/create the referenced runtime namespace.
  (when (and (seq? form) (= 'ns (first form)))
    (loop [pending [form]]
      (when (seq pending)
        (let [x (peek pending) pending (pop pending)]
          (when (vector? x)
            (doseq [i (range (dec (count x)))
                    :when (#{:as :as-alias} (nth x i))
                    :let [alias-name (nth x (inc i))]]
              (when-not (symbol? alias-name) (fail! "Invalid source reader alias" {}))
              (.addAlias ^clojure.lang.Namespace reader-ns alias-name reader-ns)))
          (recur (if (coll? x) (into pending x) pending)))))))
(defn- read-forms [file]
  (let [reader-ns (create-ns (gensym "build-audit.reader-"))]
    (try
      (with-open [reader (java.io.PushbackReader. (io/reader file))]
        (binding [*ns* reader-ns *read-eval* false *data-readers* {}
                  *default-data-reader-fn* (fn [tag _] (fail! "Tagged source reader is not audited" {:tag tag}))]
          (refer 'clojure.core)
          (let [eof (Object.)]
            (loop [forms []]
              (let [form (read {:eof eof :read-cond :allow :features #{:clj}} reader)]
                (if (identical? eof form) forms
                  (do (reader-aliases! reader-ns form) (recur (conj forms form)))))))))
      (finally (remove-ns (ns-name reader-ns))))))

(defn- source-info [path file]
  (let [forms (read-forms file)
        source-ns (some #(when (and (seq? %) (= 'ns (first %))) (second %)) forms)
        definitions (into #{} (keep #(when (and (seq? %) (#{'def 'defonce 'defn 'defn-} (first %)))
                                      (second %))) forms)]
    (when-not (symbol? source-ns) (fail! "Missing source namespace" {:source path}))
    {:namespace source-ns :definitions definitions
     :dynamic
     (loop [pending forms found #{}]
       (if (empty? pending) found
         (let [x (peek pending) pending (pop pending)]
           (cond
             (and (seq? x) (resolver-symbol? (first x)))
             (let [target (second x)]
               (when-not (and (#{'requiring-resolve 'clojure.core/requiring-resolve} (first x))
                              (= 2 (count x)) (seq? target) (= 2 (count target))
                              (= 'quote (first target)) (symbol? (second target))
                              (namespace (second target)))
                 (fail! "Computed dynamic resolution is not packaged" {:source path}))
               (recur pending (conj found {:source path :var (second target) :feature :typed-compiler})))
             ;; Inert quoted examples are not load sites.
             (and (seq? x) (= 'quote (first x))) (recur pending found)
             (resolver-symbol? x)
             (fail! "Indirect dynamic resolver is not packaged" {:source path})
             (map? x) (recur (into pending (mapcat identity x)) found)
             (coll? x) (recur (into pending x) found)
             :else (recur pending found)))))}))

(defn verify!
  "Additional closed schema and dynamic resolution audit. Literal/resource checks
   remain the build's existing verify-closure! responsibility. ROOT is explicit so
   negative inventory tests need neither Pattern nor a core jar."
  [closure runtime-root module-root]
  (when-not (and (= #{:schema :sources :resources :java :dynamic-resolves :compiler-profile} (set (keys closure)))
                 (= "lean-runtime-closure/2" (:schema closure))
                 (= pattern-profile (:compiler-profile closure))
                 (vector? (:sources closure)) (vector? (:resources closure))
                 (vector? (:dynamic-resolves closure))
                 (= (count (:sources closure)) (count (set (:sources closure)))))
    (fail! "Invalid optional runtime inventory" {}))
  (let [declared (:dynamic-resolves closure)]
    (when-not (and (= (count declared) (count (set declared)))
                   (every? #(and (map? %) (= #{:source :var :feature} (set (keys %)))
                                  (some #{(:source %)} (:sources closure))
                                  (symbol? (:var %)) (namespace (:var %))
                                  (= :typed-compiler (:feature %))) declared))
      (fail! "Invalid dynamic resolution inventory" {}))
    (let [runtime (into {} (map (fn [path] [path (source-info path (io/file runtime-root path))])) (:sources closure))
          module (into {} (for [file (file-seq (io/file module-root))
                               :when (and (.isFile file) (re-find #"\.cljc?$" (.getName file)))]
                           [(.getPath file) (source-info (.getPath file) file)]))
          observed (into #{} (mapcat :dynamic) (concat (vals runtime) (vals module)))
          by-ns (into {} (map (juxt :namespace identity)) (vals runtime))]
      (when-not (= (count by-ns) (count runtime))
        (fail! "Duplicate staged source namespace" {}))
      (when-not (= (set declared) observed)
        (fail! "Dynamic resolution inventory mismatch" {:declared (set declared) :observed observed}))
      (doseq [{target :var} declared
              :let [info (get by-ns (symbol (namespace target)))]]
        (when-not (and info (contains? (:definitions info) (symbol (name target))))
          (fail! "Unstaged dynamic target Var" {:var target})))
      {:sources (count runtime) :dynamic-resolves (count observed)})))
