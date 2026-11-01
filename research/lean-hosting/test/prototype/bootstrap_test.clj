(ns prototype.bootstrap-test
  (:require [clojure.test :refer [deftest is]]
            [clojure.java.io :as io]
            [prototype.bootstrap :as bootstrap]
            [prototype.interop :as interop]
            [prototype.module-runtime :as modules]
            [prototype.import-ir :as ir]
            [prototype.machine :as m]
            [ansatz.export.replay :as replay])
  (:import [java.nio.file Files]))

(def imported ["str" ["anonymous"] "Imported"])
(def main-module ["str" ["anonymous"] "Small"])
(defn- name-in [parent part] ["str" parent part])
(def base (name-in imported "base"))
(def local (name-in main-module "local"))
(def entry (name-in main-module "answer"))
(def host (name-in main-module "host"))
(def unused (name-in main-module "unused"))
(def unknown (name-in main-module "unknown"))
(def nat-add ["str" ["anonymous"] "natAdd"])
(defn- arg [i] {:var {:id {:idx i}}})
(defn- param [i] {:x {:idx i} :ty "object" :borrow false})
(defn- declaration [name params body role source-module]
  {:kind "decl" :name name :sourceLocal true :sourceModule source-module
   :dependencies [] :runtime {:role role}
   :ir {:fdecl {:f name :xs params :type "object" :body body}}})
(defn- extern [name symbol params]
  {:kind "decl" :name name :dependencies [] :runtime {:role "ordinary"}
   :ir {:extern {:f name :xs params :type "tobject"
                 :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"] :fn symbol}}]}}}})
(defn- manifest [module imports actions]
  {:schema "lean-ir-probe/1" :leanVersion "4.33.1"
   :runtimeProfile {:wordBits 64 :target "x86_64-unknown-linux-gnu"}
   :exports []
   :initializationPlan {:schema "lean-init-plan/1" :module module :moduleSystem false
                        :imports imports :actions (mapv (fn [name] {:action {:kind "value" :name name :target name}
                                                                   :meta false}) actions)}})
(defn- tiny-catalogues []
  (let [base-row (declaration base [] ["vdecl" {:idx 0} "object" {:lit {:v {:num {:v 40}}}}
                                      ["ret" (arg 0)]] "value" imported)
        local-row (declaration local [] ["vdecl" {:idx 0} "object" {:fap {:c base :ys []}}
                                        ["ret" (arg 0)]] "value" main-module)
        unused-row (declaration unused [] ["vdecl" {:idx 0} "object" {:pap {:c unknown :ys []}}
                                          ["ret" (arg 0)]] "value" main-module)
        entry-row (declaration entry [(param 0)]
                               ["vdecl" {:idx 1} "object" {:fap {:c local :ys []}}
                                ["vdecl" {:idx 2} "object" {:fap {:c nat-add :ys [(arg 1) (arg 0)]}}
                                 ["vdecl" {:idx 3} "object" {:fap {:c host :ys [(arg 2)]}}
                                  ["ret" (arg 3)]]]] "ordinary" main-module)
        imported-copy (-> base-row (assoc :sourceLocal false :sourceModule nil) (assoc-in [:runtime :role] "ordinary"))
        rows [local-row unused-row entry-row imported-copy
              (extern host "test_bootstrap_host" [(param 0)])
              (extern unknown "test_bootstrap_unimplemented" [(param 0)])
              (assoc-in (extern nat-add "lean_nat_add" [{:x {:idx 0} :ty "tobject" :borrow true}
                                                         {:x {:idx 1} :ty "tobject" :borrow true}])
                        [:ir :extern :type] "tobject")]]
    {:imports {:manifests [(manifest imported [] [base])] :declarations {base base-row}}
     :file {:manifests [(manifest main-module [{:module imported :meta false}] [local unused])]
            :declarations (into {} (map (juxt :name identity)) rows)}}))

(def bindings {"test_bootstrap_host" {:arguments [:nat] :result :nat :fn (fn [_ n] (inc n))}})

(defn- with-loader [source-catalogue f]
  (let [directory (.toFile (Files/createTempDirectory "ansatz-bootstrap-test-" (make-array java.nio.file.attribute.FileAttribute 0)))
        commands (atom [])
        options {:module "Small" :roots ["Small.answer"] :bindings bindings
                 :source-root (str directory) :build-root (str (io/file directory "compiled"))
                 :entropy {:bytes [1 2 3 4] :position 1}
                 :environment {"ANSATZ_BOOTSTRAP_TEST" "snapshot-value"}}]
    (try
      (with-redefs-fn {#'bootstrap/command!
                      (fn [stage args env]
                        (swap! commands conj {:stage stage :args args :env env})
                        (if (= :toolchain stage) "/mock/pinned-lean\n" "mock-output\n"))
                      #'ir/index-bundles (fn [_] source-catalogue)}
        #(f options commands))
      (finally
        (doseq [file (reverse (file-seq directory))] (.delete ^java.io.File file))))))

(deftest imported-initialization-overlays-raw-and-indexed-catalogues
  (let [{:keys [imports file]} (tiny-catalogues)
        reads (atom [])
        indexed (assoc imports :declarations {base "opaque-index-entry"}
                       :read-declaration (fn [name] (swap! reads conj name) (get-in imports [:declarations name])))]
    (doseq [backend [:reference :mutable :jvm] imported-catalogue [imports indexed]]
      (with-loader file
        (fn [options commands]
          (let [session (bootstrap/load-file! (assoc options :initialize-imports true
                                                    :import-catalogue imported-catalogue :backend backend))
                native-export (second @commands)]
            (is (= [:toolchain :ir-export] (mapv :stage @commands)))
            (is (some #{"--source"} (:args native-export)))
            (is (some #{"--olean"} (:args native-export)))
            (is (some #{"--local"} (:args native-export)))
            (is (not-any? #{"--closure"} (:args native-export)))
            (is (= :native-bootstrap (:frontend session)))
            (is (= :imports (:initialization session)))
            (is (= :unchecked (:kernel-status session)))
            (is (= 43 (:value (interop/call session "Small.answer" [2]))))
            (is (= 43 (:value (interop/call session "Small.answer" [2]))))
            (is (= 40 (get-in session [:initial-world :globals base :value])))
            (is (= #{[imported :all] [main-module :all]} (get-in session [:initial-world :initialized-modules])))
            (is (= {:bytes [1 2 3 4] :position 1} (get-in session [:initial-world :entropy])))
            (is (= {:source :provided :capacity 4 :initial-position 1 :forks :replay} (:entropy-input session)))
            (is (= :snapshot (:environment-input session)))
            (is (= {"ANSATZ_BOOTSTRAP_TEST" "snapshot-value"} (get-in session [:initial-world :environment])))
            (is (some? (get-in session [:functions unknown :deferred-extern])))
            (is (= "value" (get-in imports [:declarations base :runtime :role])))
            (is (= "ordinary" (get-in file [:declarations base :runtime :role])))))))
    (is (seq @reads))))

(deftest missing-producer-plans-fail-explicitly
  (let [{:keys [imports file]} (tiny-catalogues)]
    (with-loader file
      (fn [options commands]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"requires an import-catalogue"
                             (bootstrap/load-file! (assoc options :initialize-imports true))))
        (is (empty? @commands))
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing producer module"
                             (bootstrap/load-file! (assoc options :initialize-imports true
                                                         :import-catalogue (assoc imports :manifests [])))))))))

(deftest strict-kernel-checking-precedes-guest-initialization
  (let [{:keys [imports file]} (tiny-catalogues)]
    (with-loader file
      (fn [options _]
        (with-redefs [replay/replay-file-streaming (fn [_] {:stats {:errors 1} :error-names ["bad"]})
                      modules/link (fn [& _] (throw (AssertionError. "Initialization linkage ran before kernel gate")))]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Ansatz rejected"
                               (bootstrap/load-file! (assoc options :initialize-imports true :import-catalogue imports
                                                           :kernel-exporter "mock-exporter")))))))))

(deftest default-and-local-only-loader-paths-remain-native-bootstrap
  (let [identity-row (declaration entry [(param 0)] ["ret" (arg 0)] "ordinary" main-module)
        catalogue {:manifests [(manifest main-module [] [])] :declarations {entry identity-row}}]
    (doseq [locals? [false true]]
      (with-loader catalogue
        (fn [options commands]
          (let [session (bootstrap/load-file! (assoc options :initialize-locals locals?))]
            (is (= (if locals? [:toolchain :ir-export] [:toolchain :compile :ir-export]) (mapv :stage @commands)))
            (is (= 42 (:value (interop/call session "Small.answer" [42]))))
            (is (= :native-bootstrap (:frontend session)))
            (is (= (when locals? :local) (:initialization session)))
            (is (= {:bytes [1 2 3 4] :position 1} (get-in session [:initial-world :entropy])))))))))

(deftest entropy-is-seeded-once-or-validated-before-execution
  (let [identity-row (declaration entry [(param 0)] ["ret" (arg 0)] "ordinary" main-module)
        catalogue {:manifests [(manifest main-module [] [])] :declarations {entry identity-row}}]
    (with-loader catalogue
      (fn [options _]
        (let [session (bootstrap/load-file! (dissoc options :entropy))
              before (:initial-world session)
              first-call (interop/call session "Small.answer" [42])
              second-call (interop/call session "Small.answer" [42])]
          (is (= 1024 (count (get-in before [:entropy :bytes]))))
          (is (every? #(<= 0 % 255) (get-in before [:entropy :bytes])))
          (is (= :host-secure-random (get-in session [:entropy-input :source])))
          (is (= (get-in first-call [:state :entropy]) (get-in second-call [:state :entropy]) (:entropy before))))
        (doseq [entropy [nil {:bytes [256]} {:bytes [0] :position 2} {:bytes '(1 2)}]]
          (is (thrown? clojure.lang.ExceptionInfo (bootstrap/load-file! (assoc options :entropy entropy)))))))))

(deftest imported-initializers-consume-the-explicit-entropy-input-once
  (let [{:keys [imports file]} (tiny-catalogues)
        seed-name (name-in main-module "seed")
        seed-fn (name-in main-module "initializeSeed")
        random-fn (name-in main-module "randomBytes")
        random-row (-> (extern random-fn "lean_io_get_random_bytes"
                               [{:x {:idx 0} :ty "usize" :borrow false}
                                {:x {:idx 1} :ty "void" :borrow false}])
                       (assoc-in [:ir :extern :type] "object"))
        seed-row (-> (declaration seed-name [] ["unreachable"] "initialized" main-module)
                     (assoc-in [:runtime :initializer] seed-fn))
        initializer (declaration seed-fn [{:x {:idx 0} :ty "void" :borrow false}]
                                 ["vdecl" {:idx 1} "usize" {:lit {:v {:num {:v 2}}}}
                                  ["vdecl" {:idx 2} "object" {:fap {:c random-fn :ys [(arg 1) "erased"]}}
                                   ["ret" (arg 2)]]] "ordinary" main-module)
        file (-> file
                 (update :declarations into (map (juxt :name identity) [random-row seed-row initializer]))
                 (update-in [:manifests 0 :initializationPlan :actions] conj
                            {:action {:kind "initialize" :name seed-name :target seed-fn} :meta false}))]
    (doseq [backend [:reference :mutable :jvm]]
      (with-loader file
        (fn [options _]
          (let [session (bootstrap/load-file! (assoc options :initialize-imports true :import-catalogue imports :backend backend))
                world (:initial-world session)
                seed (get-in world [:globals seed-name :value])
                left (interop/call session "Small.answer" [2])
                right (interop/call session "Small.answer" [2])]
            (is (= [2 3] (:bytes (m/node world seed))))
            (is (= 0 (:rc (m/node world seed))))
            (is (= 3 (get-in world [:entropy :position])))
            (is (= (:entropy world) (get-in left [:state :entropy]) (get-in right [:state :entropy])))))))))

(deftest guest-environment-is-an-immutable-explicit-or-inherited-snapshot
  (let [identity-row (declaration entry [(param 0)] ["ret" (arg 0)] "ordinary" main-module)
        catalogue {:manifests [(manifest main-module [] [])] :declarations {entry identity-row}}]
    (with-loader catalogue
      (fn [options _]
        (let [session (bootstrap/load-file! (dissoc options :environment))
              snapshot (get-in session [:initial-world :environment])]
          ;; Do not print inherited environment values, even on test failure.
          (is (true? (= snapshot (into {} (System/getenv)))))
          (is (= :snapshot (:environment-input session))))
        (doseq [environment [nil {"key" nil} {:keyword "value"} {"key" 1}]]
          (is (thrown-with-msg? clojure.lang.ExceptionInfo #"map strings to strings"
                               (bootstrap/load-file! (assoc options :environment environment)))))))))
