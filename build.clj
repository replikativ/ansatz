;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Build script for compiling Java sources.

(ns build
  (:require [clojure.tools.build.api :as b]))

(defn javac
  "Compile Java sources from src-java/ to classes/."
  [_]
  (b/javac {:src-dirs ["src-java"]
            :class-dir "classes"
            :basis (b/create-basis {:project "deps.edn"})
            :javac-opts ["-source" "11" "-target" "11"]}))

(defn clean
  "Remove compiled classes."
  [_]
  (b/delete {:path "classes"}))
