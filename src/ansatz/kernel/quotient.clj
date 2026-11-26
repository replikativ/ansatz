(ns ansatz.kernel.quotient
  "Atomic import of Lean's canonical quotient package. Lean kernel/quot.cpp's
   add_quot checks the existing Eq family and generates all four primitives.
   Imports instead validate every supplied primitive before publishing a new Env."
  (:import [ansatz.kernel ConstantInfo Env TypeChecker]))

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
  "Check the already admitted Eq family before quotient initialization: the kernel's
   structural check, Lean's check_eq_type (quot.cpp)."
  [^Env checked]
  (TypeChecker/checkQuotEq checked)
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
