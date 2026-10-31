(ns original-build-identity-provider-checks-v1
  "Real tiny JVM HostRequests; source lease/lookup modeled explicitly. No image."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.data.json :as json] [clojure.java.io :as io]
            [java-ir-baseline :as j]
            [original-build-identity-provider-v1 :as provider]
            [ansatz.research.ir.source-setup :as source]))
(def ^:dynamic *basis* nil)
(def directory (io/file (.getParentFile (io/file *file*)) "../data/build-identity"))
(defn entries []
  (into {} (for [[symbol spec] provider/specifications
                 :let [r (json/read-str (slurp (io/file directory (str symbol ".json"))))]]
             [(:name spec) {:row (get r "row") :sha256 (get r "sha256")}])))
(defn reject? [f] (try (f) false (catch Exception _ true)))
(defn fixture [symbol enabled?]
  (let [spec (get provider/specifications symbol) entry (get (entries) (:name spec))
        base (j/prepare-host-program *basis* [] [(select-keys spec [:symbol :parameters :borrowed :result])])
        src (j/source-binding base (Object.)) h (j/declaration-header src (:row entry) (:sha256 entry))
        ctx (cond-> (j/register-headers base [h]) enabled? (assoc :build-identity (j/supported-build-identity base)))
        engine (j/machine ctx)]
    {:ctx ctx :engine engine :source src :spec spec
     :session {:driver {:engine engine :source src :current-ctx (atom ctx)}}}))
(defn boundary! [{:keys [ctx engine]} wanted]
  (loop [left 100]
    (if (= wanted (j/phase ctx engine)) true
      (do (assert (pos? left)) (j/advance! ctx engine 10) (recur (dec left))))))
(defn start! [{:keys [ctx engine spec] :as f} unit]
  (j/start! ctx engine (source/label (:name spec)) [unit])
  (boundary! f "host-call")
  (j/host-request ctx engine))
(defn modeled-source [f]
  (let [rows (entries)]
    (with-redefs [source/lookup-entry (fn [_ name] (get rows name))
                  source/guard-source! (fn [_ _] nil)] (f))))
(deftest exact-original-family-and-metadata-drift
  (let [rows (entries) receipt (Object.)]
    (with-redefs [source/lookup-entry (fn [_ name] (get rows name))]
      (is (= 5 (count (provider/early-specifications! receipt)))))
    (doseq [[name entry] rows
            change [#(assoc % :sha256 (apply str (repeat 64 "0")))
                    #(assoc-in % [:row "ir" "extern" "xs" 0 "borrow"] true)
                    #(assoc-in % [:row "runtime" "initializer"] true)
                    #(assoc-in % [:row "dependencies"] [["anonymous"]])]]
      (with-redefs [source/lookup-entry (fn [_ n] (if (= name n) (change entry) (get rows n)))]
        (is (reject? #(provider/early-specifications! receipt)))))))
(deftest all-five-real-requests-reply-with-supported-build-values
  (modeled-source
    (fn []
      (doseq [[symbol spec] provider/specifications
              :let [{:keys [ctx engine session] :as f} (fixture symbol true)]]
        (try
          (let [request (start! f 0) result (provider/serve! (Object.) session)]
            (is (= :build-identity-replied (:status result)))
            (is (= symbol (:symbol result)))
            (boundary! f "complete")
            (is (= (:value spec) (j/take-result! ctx engine)))
            (is (= "idle" (j/phase ctx engine)))
            (is (reject? #(provider/serve! (Object.) session))))
          (finally (j/close! ctx engine)))))))
(deftest absent-profile-and-nonunit-leave-actual-request-unclaimed
  (modeled-source
    (fn []
      (doseq [[enabled? unit] [[false 0] [true 1]]
              :let [{:keys [ctx engine session spec] :as f} (fixture "lean_version_get_special_desc" enabled?)]]
        (try
          (let [request (start! f unit)]
            (is (reject? #(provider/serve! (Object.) session)))
            (is (identical? request (j/host-request ctx engine)))
            (is (= "host-call" (j/phase ctx engine)))
            ;; Test-only trusted host completion to retire this rejected fixture.
            (j/resume-host! ctx engine request (:value spec))
            (boundary! f "complete")
            (j/take-result! ctx engine))
          (finally (j/close! ctx engine)))))))
(defn check! [basis]
  (binding [*basis* basis] (run-tests 'original-build-identity-provider-checks-v1)))
