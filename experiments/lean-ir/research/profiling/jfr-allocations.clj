(ns object-profile.jfr
  (:require [clojure.data.json :as json])
  (:import [jdk.jfr FlightRecorder]
           [jdk.jfr.consumer RecordingFile]
           [java.nio.file Paths]))

(defn snapshot! [output]
  (let [path (Paths/get (str output "/snapshot.jfr") (make-array String 0))
        recording (first (.getRecordings (FlightRecorder/getFlightRecorder)))]
    (.dump recording path)
    (with-open [file (RecordingFile. path)]
      (loop [result {:sample-count 0 :class-weights {} :stack-weights {}}]
        (if (.hasMoreEvents file)
          (let [event (.readEvent file)]
            (if (= "jdk.ObjectAllocationSample" (.getName (.getEventType event)))
              (let [weight (.getLong event "weight")
                    cls (.getName (.getClass event "objectClass"))
                    frames (some-> event .getStackTrace .getFrames)
                    frame (some (fn [frame]
                                  (let [m (.getMethod frame) type (.getName (.getType m))]
                                    (when (or (.startsWith type "prototype.") (.startsWith type "object_profile"))
                                      (str type "/" (.getName m))))) frames)]
                (recur (-> result (update :sample-count inc)
                           (update-in [:class-weights cls] (fnil + 0) weight)
                           (update-in [:stack-weights (or frame "other")] (fnil + 0) weight))))
              (recur result)))
          (do (spit (str output "/jfr-allocation-summary.json") (json/write-str result))
              {:sample-count (:sample-count result)
               :top-classes (take 10 (sort-by val > (:class-weights result)))
               :top-stacks (take 12 (sort-by val > (:stack-weights result)))}))))))
