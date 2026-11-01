(ns java-ir-genuine-provider
  "One retained-provider experiment. Definitions only; no bootstrap on load."
  (:refer-clojure :exclude [run!])
  (:require [clojure.string :as str]
            [java-ir-pure-provider :as provider]
            [prototype.resident-frontend :as resident]))

(defonce ^:private state (atom {:phase :ready :contexts [] :events [] :calls []}))
(defn checkpoint "Borrow private evidence; never print or serialize." [] @state)
(defn- ensure! [condition message] (when-not condition (throw (ex-info message {}))))
(defn- digest [^String text]
  (.formatHex (java.util.HexFormat/of)
              (.digest (java.security.MessageDigest/getInstance "SHA-256")
                       (.getBytes text java.nio.charset.StandardCharsets/UTF_8))))
(defn- lean-name [last]
  (provider/kernel-name ["str" ["str" ["anonymous"] "GraphChainA"] last]))
(defn- retain-context! [context]
  (swap! state update :contexts conj context) context)
(defn- load-version! [base version text]
  (swap! state assoc :active [:load version])
  (let [loaded (resident/load-source base
                                   {:text text :file-name "GraphChainA.lean"
                                    :module-name (provider/kernel-name ["str" ["anonymous"] "GraphChainA"])
                                    :roots [(lean-name "nat") (lean-name "text")] :initialization :defer})]
    ;; Retain actual returned owners BEFORE validating success or diagnostics.
    (swap! state assoc-in [:versions version] loaded)
    (retain-context! (:context loaded))
    (ensure! (:success loaded) "Genuine hosted source loading failed")
    (ensure! (:file loaded) "Successful source load lacks admitted handle")
    (swap! state assoc-in [:sources version] (digest text))
    loaded))
(defn- call! [selector version function descriptor value expected]
  (swap! state assoc :active [:call version function])
  (let [loaded (get-in @state [:versions version])
        before (count (filter #(= :completion (:event %)) (:events @state)))
        called (resident/call-with-executor (:context loaded) (:file loaded) (lean-name function)
                                            [value] {:arguments [descriptor] :result descriptor} selector)]
    (retain-context! (:context called))
    (swap! state update :calls conj {:version version :function function :value (:value called)})
    (ensure! (= expected (:value called)) "Genuine Java result differs")
    (ensure! (= (inc before) (count (filter #(= :completion (:event %)) (:events @state))))
             "Call completed without Java tier evidence")
    nil))
(defn summary []
  (select-keys @state [:phase :active :sources :calls :events :managed-context-close-count]))

(defn run!
  "BASE is borrowed from a live freshly checked provider. Never closes BASE or
   its backing Source. SOURCE is the exact original GraphChainA fixture. One-shot;
   failures escrow all owners and never retry. Must keep provider lease alive."
  [base basis source]
  (ensure! (= "d53a8b4270d5c8056d3f6ff3ee442820acc3bab398d692c75773ed4da210a86e" (digest source))
           "Original GraphChainA source differs")
  (let [before @state]
    (ensure! (and (= :ready (:phase before))
                  (compare-and-set! state before (assoc before :phase :running))) "Experiment unavailable"))
  (let [selector (provider/selector basis #(swap! state update :events conj %))
        big 184467440737095516160000N
        unicode "Aé€😀\u0000\n"]
    (try
      (load-version! base :original source)
      (call! selector :original "nat" :nat big big)
      (call! selector :original "text" :string unicode unicode)
      (let [edited (str/replace source "def nat (x : Nat) : Nat := x" "def nat (x : Nat) : Nat := 7")]
        (ensure! (not= edited source) "Edit did not change source")
        (load-version! base :edited edited))
      (call! selector :edited "nat" :nat big 7)
      (call! selector :original "nat" :nat 41 41)
      (call! selector :edited "text" :string unicode unicode)
      (swap! state assoc :phase :passed :active nil)
      (summary)
      (catch Throwable cause
        (swap! state assoc :phase :failed :failure cause)
        (throw cause)))))

(defn close-contexts!
  "Release successful experiment children only. Does not dispose borrowed provider.
   Failure evidence has no automatic cleanup policy."
  []
  (ensure! (= :passed (:phase @state)) "Only completed experiment supports managed close")
  (doseq [context (reverse (:contexts @state))]
    (resident/close! context)
    (swap! state update :managed-context-close-count (fnil inc 0)))
  (swap! state assoc :contexts [] :phase :closed)
  (summary))
