;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Build script for ansatz — compile Java kernel, build JAR, deploy.

(ns build
  (:refer-clojure :exclude [test])
  (:require [clojure.tools.build.api :as b]
            [deps-deploy.deps-deploy :as dd])
  (:import [clojure.lang ExceptionInfo]))

(def org "replikativ")
(def lib 'org.replikativ/ansatz)
(def current-commit (b/git-process {:git-args "rev-parse HEAD"}))
(def version (format "0.2.%s" (b/git-count-revs nil)))
(def class-dir "target/classes")
(def basis (b/create-basis {:project "deps.edn"}))
(def jar-file (format "target/%s-%s.jar" (name lib) version))

(defn clean [_]
  (b/delete {:path "target"})
  (b/delete {:path "classes"}))

(defn javac
  "Compile Java sources from src-java/ to classes/."
  [_]
  (b/javac {:src-dirs ["src-java"]
            :class-dir "classes"
            :basis basis
            :javac-opts ["-source" "11" "-target" "11"]}))

(def aot-excluded
  "Namespaces that must load from SOURCE, not be compiled into the jar: they require an
   OPTIONAL dependency that is not on the library's own classpath (ansatz.malli loads lazily
   when malli is on the consumer's)."
  '#{ansatz.malli})

(defn- aot-namespaces
  "Every namespace under src/, minus `aot-excluded`."
  []
  (->> (file-seq (java.io.File. "src"))
       (filter #(.endsWith (.getName ^java.io.File %) ".clj"))
       (map #(-> (.getPath ^java.io.File %) (subs 4)
                 (clojure.string/replace #"\.clj$" "")
                 (clojure.string/replace "/" ".")
                 (clojure.string/replace "_" "-")
                 symbol))
       (remove aot-excluded)
       sort
       vec))

(def uber-file "target/ansatz-standalone.jar")

(defn jar [_]
  (javac nil)
  (b/write-pom {:class-dir class-dir
                :lib lib
                :version version
                :basis basis
                :src-dirs ["src"]
                :scm {:url "https://github.com/replikativ/ansatz"
                      :connection "scm:git:git://github.com/replikativ/ansatz.git"
                      :developerConnection "scm:git:ssh://git@github.com/replikativ/ansatz.git"
                      :tag (str "v" version)}
                :pom-data [[:description "Verified Clojure via Lean 4 Mathlib — write Clojure, prove it correct"]
                           [:url "https://github.com/replikativ/ansatz"]
                           [:licenses
                            [:license
                             [:name "Apache License 2.0"]
                             [:url "https://www.apache.org/licenses/LICENSE-2.0"]]]
                           [:developers
                            [:developer
                             [:id "whilo"]
                             [:name "Christian Weilbach"]
                             [:email "ch_weil@topiq.es"]]]]})
  (b/copy-dir {:src-dirs ["src" "classes" "resources"]
               :target-dir class-dir})
  ;; AOT-compile ansatz's OWN namespaces into the jar. Loading them from source costs ~7.5 s
  ;; of every startup (39k lines); as classes, ~1 s. `:filter-nses` keeps it clean: only
  ;; `ansatz.*` classes are written, never a dependency's — a library that ships compiled
  ;; classes of its dependencies shadows whatever version the user resolved. (konserve and
  ;; core.async, the other ~16 s, load from source until they ship their own classes; the
  ;; zero-config path no longer loads them at all — see ansatz.core/init!*.)
  (b/compile-clj {:basis basis
                  :class-dir class-dir
                  :ns-compile (aot-namespaces)
                  :filter-nses '[ansatz]})
  (b/jar {:class-dir class-dir
          :jar-file jar-file}))

(defn jar-stable
  "`jar`, plus a copy at the fixed path the :jar-test alias depends on — the alias cannot name
   a version that changes with every commit."
  [_]
  (jar nil)
  (b/copy-file {:src jar-file :target "target/ansatz.jar"})
  (println "Wrote" jar-file "and target/ansatz.jar"))

(defn uber
  "An application uberjar with the WHOLE stack AOT-compiled — ansatz, konserve, datahike and
   core.async — not just ansatz's own namespaces.

   This is the packaging that makes startup fast, and it is safe HERE where it is not safe in a
   library: an application pins its own dependency versions, so compiling them cannot shadow a
   version someone else resolved. Measured against the plain library jar, same machine, warm
   cache:

       (require 'ansatz.core)   1.2-1.4 s  -> 0.8 s
       (init! \"mathlib\")       14.0-15.1 s -> 3.8-3.9 s
       first catalogue recall   28.9-29.6 s -> 5.1-6.2 s
       total first session      47.4-49.1 s -> 12.5-13.5 s

   The uberjar is ~50 MB: it carries the whole stack plus the bundled Init tier.

   The library jar (`jar`) stays filtered to `ansatz.*` and ships no dependency classes."
  [_]
  (clean nil)
  (javac nil)
  (let [uber-basis (b/create-basis {:project "deps.edn" :aliases [:datahike]})]
    (b/copy-dir {:src-dirs ["src" "src-datahike" "classes" "resources"] :target-dir class-dir})
    (b/compile-clj {:basis uber-basis
                    :class-dir class-dir
                    :ns-compile '[ansatz.core ansatz.search ansatz.catalogue ansatz.import]})
    (b/uber {:class-dir class-dir
             :uber-file uber-file
             :basis uber-basis}))
  (println "Wrote" uber-file))

(defn deploy
  "Deploy to Clojars. Set CLOJARS_USERNAME and CLOJARS_PASSWORD env vars."
  [_]
  (jar nil)
  (dd/deploy {:installer :remote :artifact jar-file
              :pom-file (b/pom-path {:lib lib :class-dir class-dir})}))

(defn fib [a b]
  (lazy-seq (cons a (fib b (+ a b)))))

(defn retry-with-fib-backoff [retries exec-fn test-fn]
  (loop [idle-times (take retries (fib 1 2))]
    (let [result (exec-fn)]
      (if (test-fn result)
        (do (println "Returned: " result)
            (if-let [sleep-ms (first idle-times)]
              (do (println "Retrying with remaining back-off times (in s): " idle-times)
                  (Thread/sleep (* 1000 sleep-ms))
                  (recur (rest idle-times)))
              result))
        result))))

(defn try-release []
  (try ((requiring-resolve 'borkdude.gh-release-artifact/overwrite-asset)
        {:org org
         :repo (name lib)
         :tag version
         :commit current-commit
         :file jar-file
         :content-type "application/java-archive"
         :draft false
         ;; vary the opts per attempt: gh-release-artifact memoizes release-for on its
         ;; opts map, so without this a failed lookup would be replayed on every retry
         :nonce (System/currentTimeMillis)})
       ;; catch Exception, not just ExceptionInfo: gh-release-artifact NPEs when the
       ;; GitHub list endpoint hasn't caught up with a just-created release (eventual
       ;; consistency); the backoff retry finds the release and uploads the asset.
       (catch Exception e
         (assoc (ex-data e) :failure? true :error (ex-message e)))))

(defn release [_]
  (jar nil)
  (println "Trying to release artifact...")
  (let [ret (retry-with-fib-backoff 10 try-release :failure?)]
    (if (:failure? ret)
      (do (println "GitHub release failed!")
          (System/exit 1))
      (println (:url ret)))))

(defn install [_]
  (clean nil)
  (jar nil)
  (b/install {:basis (b/create-basis {})
              :lib lib
              :version version
              :jar-file jar-file
              :class-dir class-dir}))
