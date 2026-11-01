(ns ansatz.tactic.linarith-mathlib-test
  "linarith and nlinarith over Mathlib's ordered fields (Rat, Real), with Mathlib's own
   `Mathlib.Tactic.Linarith.*` lemmas and instances synthesized. Cases are from
   MathlibTest/Tactic/Linarith/Basic.lean. Skipped when the Mathlib store is absent."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]))

(def ^:private mathlib-store
  (delay ((requiring-resolve 'ansatz.store/resolve-existing) "mathlib")))

(defn- with-mathlib [f]
  (if-let [path @mathlib-store]
    (let [saved-env @a/ansatz-env saved-idx @a/ansatz-instance-index]
      (try (binding [a/*verbose* false]
             (binding [*out* (java.io.StringWriter.)] (a/init! (str path) "mathlib"))
             (f))
           (finally (reset! a/ansatz-env saved-env)
                    (reset! a/ansatz-instance-index saved-idx))))
    (println "  (skipping linarith-mathlib-test — no mathlib store)")))

(use-fixtures :once with-mathlib)

(defmacro ^:private proves [nm params goal & tactics]
  `(is (do (a/theorem ~nm ~params ~goal ~@tactics) true) ~(str nm)))

(deftest linarith-ordered-fields
  (testing "MathlibTest/Tactic/Linarith/Basic.lean"
    (proves mlin-1 [a :- Rat, b :- Rat, c :- Rat, h1 :- (> a 0), h2 :- (> b 5), h3 :- (< c -10),
                    h4 :- (< (- (+ a b) c) 3)]
            False (linarith))
    (proves mlin-2 [a :- Rat, b :- Rat, h2 :- (> b 0), h3 :- (Not (>= b 0))] False (linarith))
    (proves mlin-3 [x :- Rat, y :- Rat, z :- Rat, hx :- (Not (> x (* 3 y))), h2 :- (Not (> y (* 2 z))),
                    h3 :- (>= x (* 6 z))]
            (= Rat x (* 3 y)) (linarith))
    (proves mlin-4 [x :- Rat, y :- Rat, h :- (< x y)] (Ne x y) (linarith))
    (proves mlin-5 [A :- Rat, B :- Rat, h :- (< 0 (* A B))] (< 0 (* (* 8 A) B)) (linarith))
    (proves mlin-6 [u :- Rat, v :- Rat, r :- Rat, s :- Rat, t :- Rat,
                    h :- (< 0 (* u (+ (+ (* t v) (* t r)) s)))]
            (< 0 (* (* (+ (* t (+ r v)) s) 3) u)) (linarith))
    (proves mlin-7 [x :- Real, y :- Real, z :- Real, h1 :- (< (+ (* 2 x) (* -3 y)) 0),
                    h2 :- (< (+ (* -4 x) (* 2 z)) 0), h3 :- (< (+ (* 12 y) (* -4 z)) 0)]
            False (linarith))
    (proves mlin-8 [a :- Real, ha :- (<= 0 a)] (<= (* 0 0) (* 2 a)) (linarith))))

(deftest nlinarith-ordered-fields
  (testing "MathlibTest/Tactic/Linarith/Basic.lean nlinarith examples"
    (proves mnlin-1 [x :- Real, y :- Real] (<= 0 (+ (* x x) (* y y))) (nlinarith))
    (proves mnlin-2 [x :- Rat, y :- Rat] (<= 0 (+ (pow x 2) (pow y 2))) (nlinarith))
    (proves mnlin-3 [x :- Rat, y :- Rat, h1 :- (= Rat (+ (* x x) (* y y)) 0)] (= Rat x 0) (nlinarith))
    (proves mnlin-4 [x :- Rat, y :- Rat, h1 :- (<= (+ (* x x) (* y y)) 0)] (= Rat y 0) (nlinarith))
    (proves mnlin-5 [x :- Real, h1 :- (<= -1048576 x), h2 :- (<= x 1048576)]
            (<= (* x x) 1099511627776) (nlinarith))))
