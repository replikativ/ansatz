(ns ansatz.lean-compiler-options-test
  "Clojure facade lease/failure model; no Java DTO or frontend acceptance implied."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.lean :as lean]
            [prototype.resident-preparation :as preparation]
            [prototype.resident-frontend :as resident]))

(defn failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo cause cause)))
(defn packet [lease] {:candidate {:owned :environment} :configuration {:independent :registries} :source-lease lease})

(deftest compiler-options-child-preserves-borrowed-provider-scope-and-exact-failure
  (let [lease-closes (atom 0) closed (atom []) seen (atom [])
        lease (reify java.io.Closeable (close [_] (swap! lease-closes inc)))
        selection {:scalar-wrappers {}}
        original (ex-info "stale compiler selection" {:checkpoint {:exact :world} :checkpoint-session :session})]
    (with-redefs [preparation/open-checked (fn [& _] :root)
                  resident/with-compiler-options (fn [r options]
                                                   (swap! seen conj [r options])
                                                   (if (= :bad options) (throw original) [r options]))
                  resident/close! #(swap! closed conj %)]
      (let [root (lean/open {:provider (fn [_] (packet lease))})
            selected (lean/with-compiler-options root selection)
            cleared (lean/with-compiler-options selected {})]
        (try
          (is (= [[:root selection] [[:root selection] {}]] @seen))
          (let [error (failure #(lean/with-compiler-options selected :bad))]
            (is (identical? original (.getCause error)))
            (is (identical? original (lean/failure-cause (:lean/failure (ex-data error)))))
            (is (= {:exact :world} (:checkpoint (ex-data original)))))
          (lean/close! root)
          (is (= :closed-context (:lean/code (ex-data (failure #(lean/with-compiler-options root {}))))))
          (with-open [child (lean/with-compiler-options selected {})] (is child))
          (is (zero? @lease-closes))
          (finally (doseq [context [root selected cleared]] (lean/close! context))))
        (is (= 4 (count @closed)))
        (is (zero? @lease-closes))))))

