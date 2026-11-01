(ns ansatz.research.ir.bootstrap.loader
  "Small public source loader. Load artifacts.clj and definitions.clj from this
   reviewed package first; no ignored implementation files or runtime effects."
  (:require [ansatz.research.ir.bootstrap.artifacts :as artifacts]
            [ansatz.research.ir.bootstrap.definitions :as definitions]))
(defn authenticate-profile! [manifest expected-sha roots]
  (artifacts/authenticate-profile! manifest expected-sha roots))
(defn load! [profile] (definitions/load-definitions! profile))
(defn load-models! [profile] (definitions/load-models! profile))
