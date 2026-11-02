(ns ansatz.lean.jvm.compiler.bundle
  "Explicit external Linux producer bundle. SDK pins independently authorize its
   helpers; bundle self-description alone never authenticates native producers."
  (:require [ansatz.lean.jvm.compiler.transport :as transport]
            [ansatz.lean.jvm.entry :as checked-entry]
            [ansatz.lean.jvm.producer :as producer])
  (:import [java.nio.file Path Files LinkOption]))

(def supported-producers
  {"entry" {"binarySHA256" (get-in checked-entry/cohorts [1 :binary])
            "sourceSHA256" (get-in checked-entry/cohorts [1 :source])}
   "startupHeader" {"binarySHA256" "2693f971452aa28190ca5c1033bf2b1030f9703b22f53181cd0591b1ab90399c"
                    "sourceSHA256" "f8c92d652c596b9bf656135348b190a5c09cf61ec40c8775835cf180a8833dd1"}
   "typedSource" {"binarySHA256" "83342c9582dd43aef3974ffadb6f989c1f7bd23d66b3c406258ca31223030041"
                  "sourceSHA256" "a48e00225fe08c1a74b66fff1102fd0c11ecefaaafc20ddcf6e28aaf363c99d3"}})
(defn- need [ok reason]
  (when-not ok (throw (ex-info reason {:code "UnsupportedProjectConfig" :stage :native-producer-bundle}))))
(defn- child! [^Path root relative]
  (need (and (string? relative) (<= 1 (count relative) 1024)
             (not (.isAbsolute (Path/of relative (make-array String 0)))))
        "Bounded relative producer path required")
  (let [path (.resolve root relative)]
    (need (and (= path (.normalize path)) (.startsWith path root)
               (= path (.toRealPath path (make-array LinkOption 0)))
               (Files/isRegularFile path (into-array LinkOption [LinkOption/NOFOLLOW_LINKS])))
          "Producer path escapes its bundle or uses a symlink")
    path))
(defn- producer! [root name descriptor]
  (let [entry-schema (when (= "entry" name)
                       (checked-entry/schema-for-pins! (get descriptor "sourceSHA256") (get descriptor "binarySHA256")))
        supported (if entry-schema
                    (select-keys descriptor ["binarySHA256" "sourceSHA256"])
                    (supported-producers name))]
    (need (and (map? descriptor)
               (= #{"binary" "binarySHA256" "source" "sourceSHA256"} (set (keys descriptor)))
               (or entry-schema (producer/supported? name (get descriptor "sourceSHA256") (get descriptor "binarySHA256"))))
          "Producer descriptor is not an independently supported SDK cohort")
    (let [supported descriptor
          binary (child! root (get descriptor "binary")) source (child! root (get descriptor "source"))]
      (need (Files/isExecutable binary) "Producer binary is not executable")
      (need (and (= (get supported "binarySHA256")
                    (get (#'transport/file-record binary (* 256 1048576)) "sha256"))
                 (= (get supported "sourceSHA256")
                    (get (#'transport/file-record source (* 2 1048576)) "sha256")))
            "Producer binary/source bytes differ from the SDK pins")
      {:binary binary :source source :binary-sha256 (get supported "binarySHA256")
       :source-sha256 (get supported "sourceSHA256") :entry-schema entry-schema})))
(defn open!
  "Validate one explicitly supplied bundle, then configure the monitored native
   transport. No compiler is launched until the subsequent source build."
  [options]
  (let [root (#'transport/path! (.producerBundle options))
        manifest (child! root "producer-bundle.json")
        descriptor (#'transport/read-json! manifest 262144)]
    (need (and (map? descriptor) (= #{"schema" "leanCommit" "leanVersion" "target" "wordBits" "producers"}
                  (set (keys descriptor)))
               (= "lean-native-producer-bundle/1" (get descriptor "schema"))
               (= transport/lean-pin (get descriptor "leanCommit"))
               (= "4.33.1" (get descriptor "leanVersion"))
               (= "x86_64-unknown-linux-gnu" (get descriptor "target"))
               (= 64 (get descriptor "wordBits"))
               (= (set (keys supported-producers)) (set (keys (get descriptor "producers")))))
          "Unsupported native producer bundle profile")
    (let [producers (into {} (map (fn [[name value]] [name (producer! root name value)])
                                 (get descriptor "producers")))
          typed (producers "typedSource") header (producers "startupHeader") entry (producers "entry")
          compiler (transport/configure! {:sysroot (.sysroot options) :cache (.cache options)
                                          :typed-source (:binary typed)})]
      {:compiler compiler
       :project-options {:source-root "." :compile? true
                         :helper (:binary header) :helper-source (:source header)
                         :helper-sha256 (:binary-sha256 header) :helper-source-sha256 (:source-sha256 header)
                         :typed-exporter (:binary typed) :typed-exporter-source (:source typed)
                         :typed-exporter-sha256 (:binary-sha256 typed) :typed-exporter-source-sha256 (:source-sha256 typed)}
       :evidence-options {:entry-schema (:entry-schema entry)
                          :entry-helper (:binary entry) :entry-helper-source (:source entry)
                          :entry-helper-sha256 (:binary-sha256 entry) :entry-helper-source-sha256 (:source-sha256 entry)}})))
