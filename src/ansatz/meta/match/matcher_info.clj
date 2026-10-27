(ns ansatz.meta.match.matcher-info
  "Lean/Meta/Match/MatcherInfo.lean (55f80e10a3).
   Imported and locally generated matchers share the :matcher-info env extension.
   Keep the established export representation: :alts is Lean's altInfos, :discrs
   contains hName?, and :unit-thunk is AltParamInfo.hasUnitThunk."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]))

(defn discr-info
  ([] (discr-info nil))
  ([h-name] {:h-name? (some-> h-name str)}))

(defn alt-param-info [num-fields num-overlaps has-unit-thunk]
  {:num-fields num-fields :num-overlaps num-overlaps :unit-thunk has-unit-thunk})

(defn matcher-info
  [num-params num-discrs alt-infos u-elim-pos discr-infos overlaps]
  {:num-params num-params :num-discrs num-discrs :alts (vec alt-infos)
   :u-elim-pos u-elim-pos :discrs (mapv :h-name? discr-infos) :overlaps (vec overlaps)})

(defn overlaps-insert
  "Lean Overlaps.insert; pairs use the companion export's [overlapping overlapped] order."
  [overlaps overlapping overlapped]
  (let [pair [overlapping overlapped]]
    (if (some #{pair} overlaps) overlaps (conj (vec overlaps) pair))))

(defn overlaps-overlapping [overlaps overlapped]
  (vec (into (sorted-set) (keep (fn [[a b]] (when (= b overlapped) a))) overlaps)))

(defn num-alts [info] (count (:alts info)))
(defn arity [info] (+ (:num-params info) 1 (:num-discrs info) (num-alts info)))
(defn get-first-discr-pos [info] (inc (:num-params info)))
(defn get-discr-range [info]
  (range (get-first-discr-pos info) (+ (get-first-discr-pos info) (:num-discrs info))))
(defn get-first-alt-pos [info] (+ (get-first-discr-pos info) (:num-discrs info)))
(defn get-alt-range [info]
  (range (get-first-alt-pos info) (+ (get-first-alt-pos info) (num-alts info))))
(defn get-motive-pos [info] (:num-params info))
(defn get-num-eqs-from-discr-infos [infos] (count (filter (comp some? :h-name?) infos)))
(defn get-num-discr-eqs [info] (count (filter some? (:discrs info))))
(defn alt-num-params [info]
  (mapv (fn [{:keys [num-fields num-overlaps unit-thunk]}]
          (+ num-fields num-overlaps (if unit-thunk 1 0) (get-num-discr-eqs info)))
        (:alts info)))

(defn install [environment infos]
  (env/update-extension environment :matcher-info {} merge infos))

(defn add-matcher-info [environment matcher-name info]
  (install environment {(str matcher-name) info}))

(defn get-matcher-info-core?
  "The extension is already local and non-blocking; retain lookup for imported names
   without Lean's match_ prefix optimization (older companion/session APIs allow these)."
  [environment decl-name]
  (get (env/get-extension environment :matcher-info {}) (str decl-name)))

(defn is-matcher-core [environment decl-name]
  (some? (get-matcher-info-core? environment decl-name)))

(defn is-matcher-app-core? [environment expr]
  (let [[f args] (e/get-app-fn-args expr)]
    (when (e/const? f)
      (when-let [info (get-matcher-info-core? environment (e/const-name f))]
        (when (>= (count args) (arity info)) info)))))

(defn is-matcher-app-core [environment expr]
  (some? (is-matcher-app-core? environment expr)))

(defn non-overlapping? [info]
  (and info (empty? (:overlaps info)) (every? (comp zero? :num-overlaps) (:alts info))))
