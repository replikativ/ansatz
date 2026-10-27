(ns ansatz.init-artifact-profile-test
  "Loader-boundary models: storage/session setup are mocked explicitly. No DB is
   opened and no large export is replayed; actual bundle snapshot stays verified."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [ansatz.bundle :as bundle]
            [ansatz.artifact-profile :as profile]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel Env]))

(deftest zero-setup-aliases-retain-the-selected-bundle-profile
  (let [prepared (atom [])]
    (with-redefs-fn {;; setup-env! is explicitly modeled below; give the loader's
                    ;; informational size report an isolated model cell as well.
                     #'a/ansatz-env (atom (Env.))
                     #'a/bundled-medium-env (fn [_] (Env.))
                     #'a/setup-env! (fn [base] (swap! prepared conj base))}
      #(binding [a/*verbose* false]
         (with-out-str
           (a/init!) (a/init! "medium") (a/init! :init-medium) (a/load-init!))))
    (is (= 4 (count @prepared)))
    (doseq [[base admission] (map vector @prepared [:trust :trust :trust :checked-export])
            :let [p (env/get-extension base profile/extension-key nil)
                  manifest (env/get-extension base :bundled-artifacts nil)]]
      (is (= profile/schema (:schema p)))
      (is (= (:artifact/cohort manifest) (get-in p [:base :cohort])))
      (is (= admission (get-in p [:base :kernel-admission]))))))

(deftest explicit-and-named-store-modes-preserve-format-one-and-retain-unknown-role-evidence
  (let [manifest {:store/format 1 :branch "mathlib" :provenance {:lean/toolchain "leanprover/lean4:v4.33.1"}}
        events (atom []) prepared (atom []) sm {:store :borrowed-model-store}
        operations {'ansatz.store/resolve-existing (fn [_] "model-store-path")
                    'ansatz.store/check-compatible! (fn [path requirements]
                                                      (swap! events conj [:compatible path requirements]) manifest)
                    'ansatz.export.storage/open-store (fn [path] (swap! events conj [:open path]) sm)
                    'ansatz.export.storage/read-derived (fn [& _] nil)
                    'ansatz.export.storage/load-env (fn [& _] (Env.))}
        actual requiring-resolve]
    (with-redefs-fn
      {#'clojure.core/requiring-resolve (fn [name] (or (get operations name) (actual name)))
       #'a/setup-env! (fn [base store _ _] (swap! prepared conj [base store]))}
      #(do (a/init! "model-store-path" "mathlib") (a/init! "mathlib")))
    (is (= [[:compatible "model-store-path" {:branch "mathlib"}] [:open "model-store-path"]
            [:compatible "model-store-path" {:branch "mathlib"}] [:open "model-store-path"]] @events))
    (doseq [[base store] @prepared
            :let [p (env/get-extension base profile/extension-key nil)]]
      (is (= 1 (get-in p [:base :store-format])))
      (is (= "mathlib" (get-in p [:base :branch])))
      (is (identical? sm (:store-map store))))))

(deftest store-init-retains-the-observed-simp-trie-value-without-a-second-read
  (let [trie {:values [] :children {}} reads (atom 0) observed (atom nil)
        operations {'ansatz.store/check-compatible! (fn [& _] {:store/format 2 :branch "library"})
                    'ansatz.export.storage/open-store (fn [_] {:store :model})
                    'ansatz.export.storage/read-derived (fn [_ _ role]
                                                          (when (= :simp-trie role)
                                                            (swap! reads inc) trie))
                    'ansatz.export.storage/load-env (fn [& _] (Env.))}
        actual requiring-resolve]
    (with-redefs-fn
      {#'clojure.core/requiring-resolve (fn [symbol] (or (get operations symbol) (actual symbol)))
       #'a/setup-env! (fn [_ _ _ derived] (reset! observed (:simp-trie derived)))}
      #(a/init! "model-store" "library"))
    (is (= 1 @reads))
    (is (identical? trie @observed))))
