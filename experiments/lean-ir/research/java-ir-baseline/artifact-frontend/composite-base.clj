(ns java-composite-artifact-base-v1
  "Closed dispatch over the existing fixed Prelude Base and the separately issued
   source-module Base. No extensible provider registry or arbitrary Env factory."
  (:require [java-matched-artifact-base-v1 :as fixed]
            [java-prelude-finalizer-lineage-v1 :as finalizer]))
(defn- source-base? [token]
  (= "java_source_module_base_v1.SourceBase" (some-> token class .getName)))
(defn- source-run? [token]
  (= "java_source_module_exchange_v1.FinalizedSourceRun" (some-> token class .getName)))
(defn- source-operation [operation]
  ;; Late loading breaks the intentional adapter -> dispatcher -> source exchange
  ;; -> M1 -> adapter cycle. The exact issuer registry still validates every token;
  ;; matching a public deftype name/constructor is never sufficient admission.
  (requiring-resolve (symbol "java-source-module-base-v1" (name operation))))
(defn guard! [token] (if (source-base? token) ((source-operation 'guard!) token) (fixed/guard! token)))
(defn with-env! [token callback]
  (if (source-base? token) ((source-operation 'with-env!) token callback) (fixed/with-env! token callback)))
(defn with-version! [token environment callback]
  (if (source-base? token) ((source-operation 'with-version!) token environment callback)
    (fixed/with-version! token environment callback)))
(defn domain-names [token]
  (if (source-base? token) ((source-operation 'domain-names) token) (fixed/domain-names token)))
(defn base-count [token]
  (if (source-base? token) ((source-operation 'base-count) token) (fixed/base-count token)))
(defn validate-base-info! [token world ops info]
  (if (source-base? token) ((source-operation 'validate-base-info!) token world ops info)
    (fixed/validate-base-info! token world ops info)))
(defn revoke! [token]
  (if (source-base? token) ((source-operation 'revoke!) token) (fixed/revoke! token)))
(defn assert-session! [token engine source run]
  (if (source-base? token) ((source-operation 'assert-session!) token engine source run)
    (fixed/assert-session! token engine source run)))
(defn finalized-view
  "Borrowed protected finalizer occurrences from one of two exact issuers only.
   The opaque Run retains owners; this function transfers none."
  [run]
  (if (source-run? run)
    ((requiring-resolve 'java-source-module-exchange-v1/with-finalized!) run identity)
    (finalizer/inspect! run)))
(defn finalized-basis [run]
  (if (source-run? run) :actual-source-closure-finalizer-only :actual-original-finalizer-only))
