(ns ansatz.lean.jvm.producer
  "Pure independently admitted non-entry producer cohorts. Never loads native services.")
(def cohorts
  {"startupHeader" #{["f8c92d652c596b9bf656135348b190a5c09cf61ec40c8775835cf180a8833dd1"
                       "2693f971452aa28190ca5c1033bf2b1030f9703b22f53181cd0591b1ab90399c"]}
   "typedSource" #{["a48e00225fe08c1a74b66fff1102fd0c11ecefaaafc20ddcf6e28aaf363c99d3"
                     "83342c9582dd43aef3974ffadb6f989c1f7bd23d66b3c406258ca31223030041"]
                    ["ac6ec4462614d39beed124c81f304b3c4875ce5fc6b15fd7b31bd0bbd56ca190" "c28866c7fcf13b141336547d4da1372ad1f90dfe46c04e5f72e5081466ce2d36"]}})
(defn supported? [role source binary] (contains? (get cohorts role) [source binary]))
(defn binary-supported? [role binary] (boolean (some #(= binary (second %)) (get cohorts role))))

(defn diagnostics-supported? [binary]
  (= "c28866c7fcf13b141336547d4da1372ad1f90dfe46c04e5f72e5081466ce2d36" binary))
