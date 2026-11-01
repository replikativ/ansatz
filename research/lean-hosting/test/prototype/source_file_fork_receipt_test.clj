(ns prototype.source-file-fork-receipt-test
  "Independent admission/fork identity regression around actual source receipts.
   Both admissions use identical native IR and therefore the same content digest;
   unit objects, executable objects and freshly checked Java CIs remain distinct.
   Calls 42/43 use DIFFERENT INPUTS with the SAME function body, not A edits.
   These model environments do NOT demonstrate semantic source edits, a resident
   frontend session, or execution of the complete Lean frontend/finalizer."
  (:require [clojure.test :refer [deftest is]]
            [prototype.source-file-typed-witness-test :as fixture]
            [prototype.machine :as m]
            [prototype.raw-interop :as raw]))

(defn independent [backend]
  (fixture/setup backend (fn [world _] world) identity))
(defn source-entry [input]
  (get-in input [:world :source-modules fixture/module-a]))
(defn installed-call [backend installed argument]
  (let [world (:world installed)
        session (raw/open-functions (:functions world) {} {:backend backend :fuel 1000000})
        root (get-in installed [:boxed-entrypoints fixture/second-name])]
    (raw/call session world root [m/erased argument])))

(deftest independently-admitted-equal-content-snapshots-have-separate-authority-and-b-calls
  (doseq [backend [:reference :mutable :jvm]]
    (let [a1 (independent backend) a2 (independent backend)
          entry1 (source-entry a1) entry2 (source-entry a2)
          ci1 (first (vals (get-in a1 [:finished :source-import-receipt :projected])))
          ci2 (first (vals (get-in a2 [:finished :source-import-receipt :projected])))
          code1 (get-in a1 [:world :functions fixture/imported-name])
          code2 (get-in a2 [:world :functions fixture/imported-name])
          b1 (fixture/install a1)
          old-result (installed-call backend b1 42)
          b2 (fixture/install a2)
          new-result (installed-call backend b2 43)
          old-again (installed-call backend b1 42)
          inherited (update a1 :world assoc :explicit-compatible-fork true)
          inherited-result (installed-call backend (fixture/install inherited) 42)]
      ;; Equal content/digest is deliberately insufficient as fork authority.
      (is (= (:unit-digest entry1) (:unit-digest entry2)))
      (is (= (:unit entry1) (:unit entry2)))
      (is (not (identical? (:unit entry1) (:unit entry2))))
      (is (= code1 code2))
      (is (not (identical? code1 code2)))
      (is (not (identical? ci1 ci2)))
      (is (= [42 43 42] (mapv :value [old-result new-result old-again])))
      (is (= 42 (:value inherited-result)))
      (is (identical? code1 (get-in inherited-result [:state :functions fixture/imported-name])))
      (is (identical? code1 (get-in old-again [:state :functions fixture/imported-name])))
      (is (identical? code2 (get-in new-result [:state :functions fixture/imported-name])))
      (is (identical? (get-in a1 [:world :source-modules])
                      (get-in old-again [:state :source-modules])))
      (is (identical? (:unit entry1)
                      (get-in old-again [:state :source-modules fixture/module-a :unit])))
      (is (= (get-in old-result [:state :heap]) (get-in old-again [:state :heap])))
      (is (= (get-in a1 [:world :globals]) (get-in old-again [:state :globals]))))))

(deftest cross-fork-unit-receipt-and-equal-body-executable-substitution-reject
  (doseq [backend [:reference :mutable :jvm]]
    (let [a1 (independent backend) a2 (independent backend)
          entry1 (source-entry a1) entry2 (source-entry a2)
          digest (:unit-digest entry1)
          receipt1 (get-in a1 [:finished :source-import-receipt])
          receipt2 (get-in a2 [:finished :source-import-receipt])
          source-path [:world :source-modules fixture/module-a]
          imported-path [:world :functions fixture/imported-name]]
      ;; Deterministic model allocations make the guest anchor IDs collide.
      ;; Fresh strict CI/Env identity must still reject a foreign receipt.
      (is (= (:anchor receipt1) (:anchor receipt2)))
      (doseq [[changed expected]
              [[(assoc-in a1 (conj source-path :unit) (:unit entry2))
                #"checked module installation authority"]
               [(assoc-in a1 [:world :eval-const-authorizations :units digest] (:unit entry2))
                #"checked module installation authority"]
               [(assoc-in a1 (conj source-path :imports) (:imports entry2))
                #"checked module installation authority"]
               [(assoc-in a1 imported-path (get-in a2 imported-path))
                #"executable differs from authorized program"]]]
        (let [progress (volatile! (:world changed))
              actual-invoke (:invoke changed)
              observed (assoc changed :invoke
                              (fn [world target args]
                                (let [[after value] (actual-invoke world target args)]
                                  (vreset! progress after) [after value])))
              failure (try (fixture/install observed) nil
                           (catch clojure.lang.ExceptionInfo cause cause))
              observed-world (or (:checkpoint (ex-data failure)) @progress)]
          (is (some? failure))
          (is (and failure (re-find expected (.getMessage failure))))
          ;; Inspect ACTUAL helper-return/error snapshots, not the untouched
          ;; persistent input map. These are borrowed input owners; retained
          ;; diagnostic result owners are not treated as permission to clean up.
          (doseq [ref [(:environment changed) (:roots changed) (:payload changed)
                       (first (:fields (m/node (:world changed) (:roots changed))))]]
            (is (= (:rc (m/node (:world changed) ref)) (:rc (m/node observed-world ref)))))))
      ;; Rejection must not revoke the separately retained legitimate snapshot.
      (is (= 42 (:value (installed-call backend (fixture/install a1) 42)))))))
