(ns ansatz.kernel.quotient
  "Atomic import of Lean's canonical quotient package. Lean kernel/quot.cpp's
   add_quot checks the existing Eq family and generates all four primitives.
   Imports instead validate every supplied primitive before publishing a new Env."
  (:require [ansatz.kernel.expr :as expr]
            [ansatz.kernel.level :as level])
  (:import [ansatz.kernel ConstantInfo Env Name TypeChecker]))

(def canonical-order ["Quot" "Quot.mk" "Quot.lift" "Quot.ind"])
(def canonical-kinds {"Quot" :type "Quot.mk" :ctor "Quot.lift" :lift "Quot.ind" :ind})

(defn validate-package!
  "Require exactly one quot-kind CI for each canonical name and matching kind.
   Return the original declarations. Does not enable quotients or change Env."
  [declarations]
  (let [names (mapv #(when (instance? ConstantInfo %) (str (.name ^ConstantInfo %))) declarations)]
    (when-not (and (= 4 (count declarations)) (= (set canonical-order) (set names))
                   (every? (fn [^ConstantInfo ci]
                             (and (.isQuot ci) (= (get canonical-kinds (str (.name ci))) (.quotKind ci))))
                           declarations))
      (throw (ex-info "Quotient import requires the complete canonical four-primitive package"
                      {:names (vec (take 8 names)) :declaration-count (count declarations)}))))
  declarations)

(defn validate-bootstrap!
  "Check the already admitted Eq family before quotient initialization, following
   native add_quot. Binder names do not affect definitional equality."
  [^Env checked]
  (let [eq-name (Name/mkStr Name/ANONYMOUS_NAME "Eq")
        ^ConstantInfo eq (.lookup checked eq-name)]
    (when-not (and eq (.isInduct eq) (= 1 (count (.levelParams eq))) (= 1 (count (.ctors eq))))
      (throw (ex-info "Quotient initialization requires the canonical checked Eq family" {})))
    (let [u (level/param (first (.levelParams eq)))
          expected (expr/forall' "α" (expr/sort' u)
                                 (expr/forall' "a" (expr/bvar 0)
                                               (expr/forall' "b" (expr/bvar 1) (expr/sort' level/zero) :default) :default) :implicit)
          ^ConstantInfo refl (.lookup checked (first (.ctors eq)))]
      (when-not (and refl (.isCtor refl) (= eq-name (.inductName refl)) (= 1 (count (.levelParams refl))))
        (throw (ex-info "Quotient initialization requires the canonical checked Eq constructor" {})))
      (let [v (level/param (first (.levelParams refl)))
            expected-refl (expr/forall' "α" (expr/sort' v)
                                        (expr/forall' "a" (expr/bvar 0)
                                                      (expr/app* (expr/const' eq-name [v]) (expr/bvar 1) (expr/bvar 0) (expr/bvar 0)) :default) :implicit)
            tc (TypeChecker. checked)]
        (when-not (and (.isDefEq tc (.type eq) expected) (.isDefEq tc (.type refl) expected-refl))
          (throw (ex-info "Quotient initialization has noncanonical Eq or constructor type" {}))))))
  checked)

(defn admit-package!
  "Validate the complete package and Eq bootstrap, then canonical primitive types
   through TypeChecker/checkConstant. Intermediate immutable Envs remain local;
   failure never publishes partially enabled quotients to the caller."
  ([checked declarations] (admit-package! checked declarations 20000000))
  ([^Env checked declarations fuel]
   (validate-package! declarations)
   (validate-bootstrap! checked)
   (let [by-name (into {} (map (fn [^ConstantInfo ci] [(str (.name ci)) ci])) declarations)]
     (reduce (fn [^Env current name] (TypeChecker/checkConstant current (get by-name name) (long fuel)))
             checked canonical-order))))
