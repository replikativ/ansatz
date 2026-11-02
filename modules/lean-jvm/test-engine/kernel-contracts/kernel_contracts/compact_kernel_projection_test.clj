(ns kernel-contracts.compact-kernel-projection-test
  (:require [clojure.test :refer [deftest is]]
            [kernel-support.compact-kernel-projection :as compact]
            [kernel-support.kernel-bridge :as bridge]
            [kernel-contracts.kernel-bridge-test :as guest]
            [kernel-support.imported-kernel :as imported]
            [kernel-contracts.imported-kernel-test :as native]
            [kernel-support.carrier :as m])
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

(defn- name-list [world name length]
  (loop [world world tail guest/nil-tag remaining length]
    (if (zero? remaining) [world tail]
      (let [[world tail] (guest/ctor world 1 [name tail] 0)]
        (recur world tail (dec remaining))))))

(defn- scratch-constants []
  ;; Projection-only data: repeated parameters are intentionally not a claimed
  ;; well-typed declaration. Distinct rows share all core expression/name refs.
  (let [[world name] (guest/guest-name (m/world {}) "scoped.probe")
        [world type] (guest/constant world "Nat")
        [world body] (guest/literal world 42)]
    (loop [world world roots [] remaining 12]
      (if (zero? remaining) {:world world :roots roots :body body}
        (let [[world params] (name-list world name 24)
              [world base] (guest/ctor world 0 [name params type] 0)
              [world all] (guest/ctor world 1 [name guest/nil-tag] 0)
              [world payload] (guest/ctor world 0 [base body guest/nil-tag all] 1)
              world (guest/scalar! world payload 0 "uint8" 1)
              [world root] (guest/ctor world 1 [payload] 0)]
          (recur world (conj roots root) (dec remaining)))))))

(deftest scoped-constant-boundary-retires-only-scratch-and-preserves-core-sharing
  (let [{:keys [world roots body]} (scratch-constants)
        original (bridge/make-projector world)
        bulk (compact/make-projector world)
        {:keys [project project-constant] :as scope} (compact/make-scoped-projector world)
        shared (:value (project world :expr body))
        counts (mapv
                 (fn [root]
                   (let [a (imported/project-constant world root original)
                         b (imported/project-constant world root bulk)
                         c (project-constant world root)]
                     (is (= (imported/checking-shape a) (imported/checking-shape b)
                            (imported/checking-shape c)))
                     (is (identical? shared (.value ^ConstantInfo c)))
                     (is (identical? shared (:value (project world :expr body))))
                     (:projected-nodes (project world :expr body)))) roots)]
    (is (= #{:project :project-constant} (set (keys scope))))
    ;; Every root has a distinct constant-val map and parameter/all list spine,
    ;; but these scratch entries do not accumulate after whole-CI completion.
    (is (apply = counts))
    (is (> (:projected-nodes (bulk world :expr body)) (last counts)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
                          (project-constant (into {} world) (first roots))))))

(deftest scoped-failed-constant-keeps-completed-children-and-clears-active-scratch
  (let [[world child] (guest/literal (m/world {}) 2)
        [world invalid] (guest/ctor world 1 [guest/nil-tag] 8)
        [world bad-type] (guest/ctor world 5 [child invalid] 8)
        [world root] (guest/declaration world "scoped.failure" bad-type child)
        original (bridge/make-projector world)
        {:keys [project project-constant]} (compact/make-scoped-projector world)
        _ (project world :nat 0)
        expected (message #(imported/project-constant world root original))]
    (is (some? expected))
    (is (= expected (message #(project-constant world root))))
    ;; The cached unrelated scalar reports current entries without materializing
    ;; CHILD. Its later lookup must add no entries: CHILD was built in failure.
    (let [after-failure (:projected-nodes (project world :nat 0))
          recovered (project world :expr child)]
      (is (= after-failure (:projected-nodes recovered)))
      (is (= expected (message #(project-constant world root))))
      (is (= after-failure (:projected-nodes (project world :nat 0))))
      (is (identical? (:value recovered) (:value (project world :expr child))))))
  (let [[world name] (guest/guest-name (m/world {}) "scoped.cycle")
        [world params] (guest/ctor world 1 [name guest/nil-tag] 0)
        [world type] (guest/literal world 1)
        [world base] (guest/ctor world 0 [name params type] 0)
        [world payload] (guest/ctor world 0 [base] 1)
        [world root] (guest/ctor world 0 [payload] 0)
        world (assoc-in world [:heap (:id params) :fields 1] params)
        {:keys [project project-constant]} (compact/make-scoped-projector world)]
    (project world :nat 0)
    (is (re-find #"Cyclic" (message #(project-constant world root))))
    (let [after-failure (:projected-nodes (project world :nat 0))]
      (is (re-find #"Cyclic" (message #(project-constant world root))))
      (is (= after-failure (:projected-nodes (project world :nat 0)))))))

(deftest scoped-complete-native-variants-match-bulk-and-original
  (let [loaded (native/loaded) world (:world loaded)
        original (bridge/make-projector world) bulk (compact/make-projector world)
        {:keys [project-constant]} (compact/make-scoped-projector world)
        entries (vec (native/entries loaded))]
    (is (= (set (range 8)) (set (map #(.tag ^ConstantInfo (:constant %)) entries))))
    (doseq [{:keys [guest]} (concat entries (reverse entries))]
      (is (= (imported/checking-shape (imported/project-constant world guest original))
             (imported/checking-shape (imported/project-constant world guest bulk))
             (imported/checking-shape (project-constant world guest)))))))

(deftest scoped-foreign-world-is-rejected-before-reading-or-retiring-scratch
  (let [world (m/world {}) foreign {:malformed :world}
        {:keys [project project-constant]} (compact/make-scoped-projector world)
        before (project world :names guest/nil-tag)
        reads (atom 0)]
    (with-redefs [imported/project-constant (fn [& _] (swap! reads inc) (throw (AssertionError. "foreign read")))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
                            (project-constant foreign (m/->Ref 123))))
      (is (zero? @reads)))
    ;; If wrong-world rejection cleared legitimate scratch, the next lookup
    ;; would allocate. Existing scratch must instead remain intact.
    (with-redefs-fn {#'compact/scratch-tables (fn [] (throw (AssertionError. "scratch was retired")))}
      #(is (= before (project world :names guest/nil-tag))))))

(deftest scoped-retirement-does-not-allocate-or-mask-the-original-failure
  (doseq [throws? [false true]]
    (let [world (m/world {})
          {:keys [project project-constant]} (compact/make-scoped-projector world)
          _ (project world :names guest/nil-tag)
          original (ex-info "original failure" {})
          allocation (ex-info "next scratch allocation" {})
          allocations (atom 0)]
      (with-redefs [imported/project-constant (fn [& _] (if throws? (throw original) :completed))]
        (with-redefs-fn {#'compact/scratch-tables (fn [] (swap! allocations inc) (throw allocation))}
          (fn []
            (if throws?
              (is (identical? original (try (project-constant world nil) nil (catch Throwable e e))))
              (is (= :completed (project-constant world nil))))
            (is (zero? @allocations))
            ;; Retirement cleared the table, without allocating a replacement.
            (is (identical? allocation (try (project world :names guest/nil-tag) nil (catch Throwable e e))))
            (is (= 1 @allocations))))))))

(deftest scoped-constant-reentry-is-rejected-before-inner-finally
  (let [world (m/world {})
        {:keys [project project-constant]} (compact/make-scoped-projector world)
        seeded (project world :names guest/nil-tag)
        calls (atom 0)]
    (with-redefs [imported/project-constant
                  (fn [& _]
                    (swap! calls inc)
                    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Reentrant constant projection"
                                          (project-constant world nil)))
                    (with-redefs-fn {#'compact/scratch-tables (fn [] (throw (AssertionError. "inner retirement")))}
                      #(is (= seeded (project world :names guest/nil-tag))))
                    :completed)]
      (is (= :completed (project-constant world nil)))
      (is (= 1 @calls)))))

(deftest explicit-default-world-reader-keeps-baseline-and-compact-semantics-shared
  (let [[world root] (guest/literal (m/world {}) 23)
        baseline (bridge/make-projector world)
        factory bridge/default-world-specification-reader
        reads (atom [])
        alternate (with-redefs [bridge/default-world-specification-reader
                                (fn [bound-world]
                                  (is (identical? world bound-world))
                                  (let [reader (factory bound-world)]
                                    (fn [kind value]
                                      (swap! reads conj [kind value])
                                      (reader kind value))))]
                    (compact/make-projector world))
        expected (baseline world :expr root)
        actual (alternate world :expr root)]
    (is (= expected actual))
    (is (= 23N (.o0 ^Expr (:value actual))))
    (is (some #(= [:expr root] %) @reads))
    (is (some #(= :literal (first %)) @reads))
    (is (some #(= :nat (first %)) @reads))
    ;; Reader carries no memo of its own; alternate traversal owns cache/cycles.
    (let [before @reads]
      (is (= actual (alternate world :expr root)))
      (is (= before @reads)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"different world"
          (alternate (into {} world) :expr root)))))
