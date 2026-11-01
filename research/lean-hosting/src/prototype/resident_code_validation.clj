(ns prototype.resident-code-validation
  "Amortize only resident executable/binding IDENTITY comparisons. This is not
   a checked-kernel, dependency-closure, initialized-unit or ownership proof.
   Unknown containers keep the original uncached validation behavior."
  (:require [prototype.import-ir :as ir])
  (:import [java.lang.ref WeakReference]
           [java.util WeakHashMap]))

(deftype ^:private CodeIdentityProof [functions bindings protectedFunctions protectedBindings])
;; Values are scalar: neither this registry nor a held proof retains code,
;; handlers, their captured Source/World, or a Context through its weak key.
;; Reloading this validator starts a fresh proof epoch; live Contexts simply
;; take the full validation path next time. No ownership or code image changes.
(def ^:private ^WeakHashMap issued (WeakHashMap.))

(defn- ordinary-map? [x]
  (or (= clojure.lang.PersistentHashMap (class x))
      (= clojure.lang.PersistentArrayMap (class x))))
(defn- frozen-keys? [x]
  (and (ordinary-map? x) (every? #'ir/frozen-target? (keys x))))

(defn- matches? [proof functions bindings protected-functions protected-bindings]
  (and (instance? CodeIdentityProof proof)
       (locking issued (true? (.get issued proof)))
       ;; A cleared reference must miss, even if a caller replaced a map by nil.
       (some? functions) (some? bindings) (some? protected-functions) (some? protected-bindings)
       (identical? functions (.get ^WeakReference (.-functions ^CodeIdentityProof proof)))
       (identical? bindings (.get ^WeakReference (.-bindings ^CodeIdentityProof proof)))
       (identical? protected-functions (.get ^WeakReference (.-protectedFunctions ^CodeIdentityProof proof)))
       (identical? protected-bindings (.get ^WeakReference (.-protectedBindings ^CodeIdentityProof proof)))))

(defn- validate-mappings! [functions bindings protected-functions protected-bindings]
  (doseq [[name function] protected-functions]
    (when-not (identical? function (get functions name))
      (throw (ex-info "Resident protected executable changed" {:name name}))))
  (doseq [[symbol binding] protected-bindings]
    (when-not (identical? binding (get bindings symbol))
      (throw (ex-info "Resident protected host capability changed" {:symbol symbol})))))

(defn validate!
  "Return an issued, weak identity proof only AFTER successful comparisons.
   A hit requires the exact four immutable maps and an actually issued object;
   copying fields into an unissued constructor instance cannot grant a hit.
   Map keys must be frozen too: mutable unrelated keys can change lookup results.
   The caller must perform its live World/session/root checks on EVERY use."
  [functions bindings protected-functions protected-bindings proof]
  (if (matches? proof functions bindings protected-functions protected-bindings)
    proof
    (do
      (validate-mappings! functions bindings protected-functions protected-bindings)
      (when (and (frozen-keys? functions) (frozen-keys? bindings)
                 (frozen-keys? protected-functions) (frozen-keys? protected-bindings))
        (let [proof (CodeIdentityProof. (WeakReference. functions) (WeakReference. bindings)
                                        (WeakReference. protected-functions) (WeakReference. protected-bindings))]
          (locking issued (.put issued proof true))
          proof)))))
