(ns prototype.compact-kernel-projection-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.compact-kernel-projection :as compact]
            [prototype.kernel-bridge :as bridge]
            [prototype.kernel-bridge-test :as guest]
            [prototype.imported-kernel :as imported]
            [prototype.imported-kernel-test :as native]
            [prototype.machine :as m])
  (:import [prototype TypedLongMemo]
           [ansatz.kernel Expr ConstantInfo]))

(deftest native-all-eight-variants-match-original-projection
  (let [loaded (native/loaded) world (:world loaded)
        original (bridge/make-projector world) compact (compact/make-projector world)
        entries (native/entries loaded)]
    (is (= (set (range 8)) (set (map #(.tag ^ConstantInfo (:constant %)) entries))))
    (doseq [{:keys [guest]} entries]
      (is (= (imported/checking-shape (imported/project-constant world guest original))
             (imported/checking-shape (imported/project-constant world guest compact)))))
    (let [payload (native/payload world (:guest (first entries)))
          constant (first (:fields (m/node world payload)))
          type (nth (:fields (m/node world constant)) 2)]
      (is (= (:projected-nodes (original world :expr type))
             (:projected-nodes (compact world :expr type)))))))

(deftest memo-handles-nil-resizing-full-width-ids-and-kind-separation
  (let [memo (TypedLongMemo.) absent (Object.) active (Object.)
        ids [Long/MIN_VALUE Long/MAX_VALUE -1 0 1 9223372036854775806]]
    (doseq [id ids kind (range 1 18)] (.put memo id (byte kind) [id kind]))
    (doseq [id ids kind (range 1 18)] (is (= [id kind] (.get memo id (byte kind) absent))))
    (.put memo 0 (byte 1) nil)
    (is (nil? (.get memo 0 (byte 1) absent)))
    (is (identical? absent (.get memo 42 (byte 1) absent)))
    (doseq [id (range 20000)] (.put memo id (byte 20) id))
    (is (> (.capacity memo) 20000))
    (doseq [id (range 20000)] (is (= id (.get memo id (byte 20) absent))))
    (doseq [id (range 1000)] (.put memo id (byte 21) active))
    (.removeValue memo active)
    (doseq [id (range 1000)]
      (is (identical? absent (.get memo id (byte 21) absent)))
      (.put memo id (byte 21) nil)
      (is (nil? (.get memo id (byte 21) absent))))
    (is (= (+ (* 6 17) 20000 1000) (.size memo)))
    (is (thrown? IllegalArgumentException (.put memo 1 (byte 0) nil)))))

(deftest shared-dags-and-cross-call-sharing-are-identical
  (let [[world lit] (guest/literal (m/world {}) 42)
        [world app] (guest/ctor world 5 [lit lit] 8)
        p (compact/make-projector world)
        first-result (p world :expr app)
        ^Expr result (:value first-result)]
    (is (identical? (.o0 result) (.o1 result)))
    (is (identical? (.o0 result) (:value (p world :expr lit))))
    (is (= 4 (:projected-nodes first-result)))
    (is (= first-result (p world :expr app)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
                          (p (into {} world) :expr app)))))

(deftest fallback-keys-preserve-original-equality-and-type-distinction
  (let [world (m/world {}) original (bridge/make-projector world) compact (compact/make-projector world)]
    (doseq [[kind value] [[:nat 0] [:nat 42N] [:nat 42] [:nat 9223372036854775808N]
                          [:name (m/->Tag 0)] [:level (m/->Tag 0)]
                          [:names (m/->Tag 0)] [:levels 0] [:string "λ😀"]]]
      (is (= (original world kind value) (compact world kind value))))
    ;; Ref extension-map fields are part of original record equality. Such
    ;; unusual refs must remain on the exact fallback path instead of aliasing.
    (let [[world lit] (guest/literal world 2) p (compact/make-projector world)
          a (p world :expr lit) b (p world :expr (assoc lit :extra true))]
      (is (= (:value a) (:value b)))
      (is (= (inc (:projected-nodes a)) (:projected-nodes b))))))

(defn message [f]
  (try (f) nil (catch Exception failure (.getMessage failure))))

(deftest malformed-layouts-cycles-and-failures-preserve-validation
  (let [[world good] (guest/literal (m/world {}) 1)
        [world invalid] (guest/ctor world 1 [guest/nil-tag] 8)
        [world cycle] (guest/ctor world 5 [good good] 8)
        [world retry-root] (guest/ctor world 5 [good invalid] 8)
        cyclic (assoc-in world [:heap (:id cycle) :fields 1] cycle)
        bad-layout (assoc-in world [:heap (:id good) :layout :ssize] 9)
        missing-bytes (assoc-in world [:heap (:id good) :scalar-bytes] {})]
    (doseq [[w kind value] [[world :expr invalid] [cyclic :expr cycle]
                            [bad-layout :expr good] [missing-bytes :expr good]
                            [world :unsupported good] [world :expr retry-root]]]
      (let [original (bridge/make-projector w) compact (compact/make-projector w)]
        (is (some? (message #(original w kind value))))
        (is (= (message #(original w kind value)) (message #(compact w kind value))))
        ;; An exception must not leave pending markers masquerading as cycles.
        (is (= (message #(original w kind value)) (message #(compact w kind value))))))
    (let [p (compact/make-projector world)]
      (is (some? (message #(p world :expr retry-root))))
      (is (= (bridge/project-with-stats world :expr good) (p world :expr good))))))

(deftest deep-projection-and-large-ref-ids
  (let [[world lit] (guest/literal (m/world {}) 0)
        high (m/->Ref Long/MAX_VALUE)
        world (assoc-in world [:heap (:id high)] (m/node world lit))
        [world root] (loop [n 0 world world value high]
                       (if (= n 10000) [world value]
                           (let [[world next] (guest/ctor world 5 [value high] 8)]
                             (recur (inc n) world next))))
        p (compact/make-projector world)
        projected (bridge/project-expr world root p)]
    (is (= 10000 (loop [n 0 ^Expr current projected]
                   (if (= Expr/APP (.tag current))
                     (recur (inc n) (.o0 current)) n))))
    (is (= 10003 (:projected-nodes (p world :expr root))))))
