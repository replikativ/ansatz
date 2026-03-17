;; Copyright (c) 2026 Christian Weilbach. All rights reserved.
;; Shared types for Ansatz export storage.

(ns ansatz.export.types
  "Shared types used by storage backends.")

;; Wrapper type for CI-shells so serialization dispatch works correctly.
;; Without this, PersistentArrayMap would intercept all small Clojure maps.
(deftype CIShell [^clojure.lang.IPersistentMap data])
