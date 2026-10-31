(ns source-import-frontend-setup-v1
  "Actual parser header setup from an issued source-closure finalizer only."
  (:require [imported-frontend-setup-v4 :as fixed]
            [java-source-module-exchange-v1 :as exchange]
            [java-ir-baseline :as j]
            [sequential-frontend-probe :as sp]
            [allocation-heartbeat-cohort-v1 :as cohort]
            [java-source-module-base-v1 :as base]
            [general-generated-batch-v1 :as batch]))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :source-import-setup-v1}))))
(defn- validate-imports! [s expected imports]
  (let [r {:driver (:driver s) :engine (sp/engine s)}
        actual (#'exchange/array-values r imports 17)]
    (need (= (count expected) (count actual)) "Parsed source imports differ from actual finalized closure roots")
    (#'exchange/scoped r
      (fn [scope]
        (doseq [[request wanted] (map vector actual expected)]
          (let [{:keys [fields bytes]} (#'exchange/ordinary r request 0 1 #{3 8})
                flags (mapv #(Byte/toUnsignedInt (aget ^bytes bytes %)) (range 3))
                wire (#'exchange/wire-name (#'exchange/typed-name scope (aget ^objects fields 0)))]
            (need (and (= [0 1 0] flags)
                       (= {:module wire :importAll false :isExported true :isMeta false} wanted))
                  "Parsed ordinary source import Name/flags/order differ")))))))
(defn setup-source!
  "Borrow the actual finalized source Env and exact closure requests. Captured
   source is still independently authenticated by the normal source provider;
   this setup parses its header genuinely, never extracts imports with a regex.
   Returns existing setup owner/failure journals without closing borrowed roots."
  [parent finalized-run captured-source]
  (let [driver (:driver parent)
        actual (exchange/with-finalized! finalized-run identity)
        closure (:closure actual) selected (exchange/with-closure! closure identity)
        _ (need (and (identical? (:engine driver) (:engine actual))
                     (identical? (:source driver) (:source actual))
                     (identical? (:current-ctx driver) (get-in selected [:driver :current-ctx])))
                "Source setup parent belongs to another finalized branch")
        text (:text captured-source) path (:path captured-source) segments (:module captured-source)
        _ (need (and (string? text) (<= (count text) 8388608)
                     (instance? java.nio.file.Path path) (vector? segments) (<= 1 (count segments) 128))
                "Bounded actual filesystem source capture required")
        check-imports (fn [session imports]
                        (exchange/with-closure! closure
                          (fn [view] (validate-imports! session (:requests view) imports))))
        result (#'fixed/setup-classic* driver (:environment actual) text (str path) segments
                 check-imports cohort/runtime-service-step!)]
    (exchange/with-finalized! finalized-run
      (fn [current]
        (need (and (identical? (:environment actual) (:environment current))
                   (identical? (:constant-map actual) (:constant-map current)))
              "Source setup changed its borrowed original finalized Env")))
    result))

(defn- ready-row! [driver name {:keys [header row]}]
  (let [ctx @(:current-ctx driver) program (:program ctx)
        bodies ^objects (#'exchange/field program "preparedBodies")
        method (.getMethod (class program) "functionId" (into-array Class [(class header)]))
        id (int (.invoke method program (object-array [header])))]
    (need (and (identical? (:source driver) (j/request-value header "source"))
               (= name (j/lean-name-data (j/request-value header "name")))
               (= name (get row "name")) (get-in row ["ir" "fdecl"])
               (<= 0 id) (< id (alength bodies)) (some? (aget bodies id)))
          "Selected imported row lacks its canonical ready Header/body")
    (aget bodies id)))
(defn- selected-code! [driver view]
  (need (and (vector? (:module-roots view)) (<= 1 (count (:module-roots view)) 16))
        "Bounded actual selected source modules required")
  (let [rows (reduce (fn [out token]
                      (exchange/with-module! token
                        (fn [m]
                          (need (and (identical? (:engine driver) (:engine m))
                                     (identical? (:source driver) (:source m)))
                                "Selected imported module belongs to another branch")
                          (reduce-kv (fn [acc name entry]
                                       (need (and (< (count acc) 2048) (not (contains? acc name)))
                                             "Selected source code overlaps or exceeds bound")
                                       (assoc acc name (assoc entry :body (ready-row! driver name entry))))
                                     out (:rows m))))) {} (:module-roots view))]
    (#'batch/ir-inventory! (into {} (map (fn [[name entry]]
                                               [name {:kind "fdecl" :declaration (get-in entry [:row "ir" "fdecl"])}]) rows)))
    rows))
(defn open-generated-scope!
  "Issue B linkage scope from its actual SourceBase/finalized closure. Imported
   code is exactly the selected modules canonical ready rows, never caller flags
   or names merely inherited in Program. Borrows all module/Run/Base resources."
  [parent adapter source-base finalized-run]
  (let [driver (:driver parent)
        check-binding! (fn []
                         (need (and (identical? (:engine driver) (:engine adapter))
                                    (identical? (:source driver) (:source adapter))
                                    (identical? source-base (:matched-base adapter))
                                    (identical? finalized-run (get-in adapter [:authority :finalized-run])))
                               "Imported scope adapter/Base/Run binding differs")
                         (base/assert-session! source-base (:engine driver) (:source driver) finalized-run))
        borrow (fn [callback]
                 (check-binding!)
                 (exchange/with-finalized! finalized-run
                   (fn [run]
                     (need (and (= :actual-source-closure-finalizer-only (:basis run))
                                (identical? (:engine driver) (:engine run))
                                (identical? (:source driver) (:source run))) "Actual source finalizer branch required")
                     (exchange/with-closure! (:closure run)
                       (fn [view]
                         (need (and (identical? (:engine driver) (:engine view))
                                    (identical? (:source driver) (:source view))) "Foreign selected closure")
                         (callback {:closure (:closure run) :modules (:module-roots view)
                                    :entries (selected-code! driver view)}))))))
        selected (borrow identity) entries (:entries selected)
        check! (fn []
                 (borrow (fn [observed]
                           (need (and (identical? (:closure selected) (:closure observed))
                                      (= (count (:modules selected)) (count (:modules observed)))
                                      (every? true? (map identical? (:modules selected) (:modules observed))))
                                 "Selected imported Closure/module identities changed")
                           (let [current (:entries observed)]
                           (need (= (set (keys entries)) (set (keys current))) "Selected imported code domain changed")
                           (doseq [[name entry] entries]
                             (let [actual (get current name)]
                               (need (and (= (:row entry) (:row actual))
                                          (identical? (:header entry) (:header actual))
                                          (identical? (:body entry) (:body actual)))
                                     "Selected imported canonical row/Header/body changed")))))))]
    (#'batch/open-scope* driver adapter {:entries entries :check! check!})))
