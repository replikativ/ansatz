(ns prototype.scalar-wrapper
  "Opt-in one-instruction scalar wrapper specialization over the existing Machine."
  (:require [prototype.runtime-abi :as abi]
            [prototype.mutable :as u]
            [prototype.machine :as m]))

(def ^:private generation (Object.))

(def ^:private modulus 18446744073709551616N)
(def ^:private maximum 18446744073709551615N)
(def ^:private descriptor-limit 64)

(defn prepare-options [options]
  (if-let [descriptors (:scalar-wrappers options)]
    (do
      (when-not (and (contains? #{clojure.lang.PersistentArrayMap clojure.lang.PersistentHashMap} (class descriptors))
                     (<= (count descriptors) descriptor-limit))
        (m/fail "Scalar wrapper descriptor budget or container" {}))
      (let [normalized (reduce-kv (fn [result name descriptor]
                                    (let [d (abi/validate-scalar-description! descriptor)]
                                      (when-not (= name (:name d)) (m/fail "Scalar wrapper descriptor key mismatch" {}))
                                      (assoc result (:name d) d))) {} descriptors)]
        (assoc options :scalar-wrappers normalized :scalar-wrapper-tokens (u/scalar-wrapper-tokens))))
    options))

(defn descriptor-for [functions body options]
  (some (fn [[name d]]
          (let [f (get functions name) params (mapv :id (:params d))
                dest (inc (reduce max 0 params))
                expected [:let dest [:runtime (:extern d) (mapv #(vector :var %) params)] [:return [:var dest]]]]
            (when (and (= params (:params f)) (= (:extern d) (:runtime-extern f))
                       (= expected (:body f)) (= expected body)) d)))
        (:scalar-wrappers options)))

(defn extension-key [functions body options]
  (when-let [d (descriptor-for functions body options)]
    [:scalar-wrapper/v1 generation (abi/scalar-description-token) d (:scalar-wrapper-tokens options)]))

(defn- carrier? [x]
  (cond (= Long (class x)) (not (neg? (long x)))
        (= clojure.lang.BigInt (class x)) (<= 0 x maximum)
        :else false))

(defn- result-value [bits]
  ;; The reference unsigned operation uses a BigInt modulus, including for small
  ;; positive results. Preserve that visible carrier at every wrapper exit.
  (if (neg? (long bits)) (+' (bigint bits) modulus) (bigint bits)))

(defn compile-wrapper [functions body options]
  (let [options (prepare-options options)]
   (when-let [d (descriptor-for functions body options)]
    (let [[a b] (mapv :id (:params d)) dest (second body) continuation (nth body 3)
          operation (:operation d) symbol (:extern d) tokens (:scalar-wrapper-tokens options)
          arithmetic (case operation :add `unchecked-add :sub `unchecked-subtract)
          abi-generation (abi/scalar-description-token)
          form `(fn [compiler-generation# abi-generation# tokens# continuation#]
                  (fn [machine#]
                    (if (and (identical? compiler-generation# generation)
                             (identical? abi-generation# (abi/scalar-description-token))
                             (u/current-scalar-wrapper? tokens# ~symbol ~operation))
                      (let [locals# (u/locals-array machine#)]
                        (if (and (< ~a (alength ^"[Ljava.lang.Object;" locals#)) (< ~b (alength ^"[Ljava.lang.Object;" locals#))
                                 (< ~dest (alength ^"[Ljava.lang.Object;" locals#))
                                 (carrier? (aget ^"[Ljava.lang.Object;" locals# ~a)) (carrier? (aget ^"[Ljava.lang.Object;" locals# ~b)))
                          (do
                            (u/add-steps! machine# 1)
                            (let [left# (.longValue ^Number (aget ^"[Ljava.lang.Object;" locals# ~a))
                                  right# (.longValue ^Number (aget ^"[Ljava.lang.Object;" locals# ~b))
                                  bits# (~arithmetic left# right#)]
                              (aset ^"[Ljava.lang.Object;" locals# ~dest (result-value bits#))
                              (u/set-body! machine# continuation#)
                              :specialized))
                          (do (u/step! machine#) :interpreted)))
                      (do (u/step! machine#) :interpreted))))
          factory (binding [*ns* (the-ns 'prototype.scalar-wrapper)] (eval form))]
      {:max-cost 1 :form form :specialization d
       :scalar-extension (extension-key functions body options) :region-limit 1
       :inlined-jumps 0 :leaf-sites 0 :compilation-attempts 1
       :execute! (factory generation abi-generation tokens continuation)}))))
