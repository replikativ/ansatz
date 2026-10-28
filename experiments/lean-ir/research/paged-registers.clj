(ns paged-registers
  "Research adapter only. Canonical valid IR, one thread, no custom helper
   callbacks or private host-storage reuse. Freeze all Machines inside scope."
  (:require [prototype.mutable :as u]
            [prototype.machine :as m])
  (:import [prototype.research PagedRegisters]
           [java.util ArrayDeque Arrays HashMap]))

(defn- paged? [x] (instance? PagedRegisters x))
(defn- width [x] (if (paged? x) (.width ^PagedRegisters x) (alength ^objects x)))
(defn- store! [x id v]
  (if (paged? x) (.set ^PagedRegisters x (int id) v) (aset ^objects x (int id) v)))

(defn with-runtime
  "THRESHOLD controls large-frame adoption. Long/MAX_VALUE is a dense adapter
   control. Runtime Var replacements are scoped; no production classes reload."
  [threshold thunk]
  (let [v #(ns-resolve 'prototype.mutable %)
        ctl @(v 'ctl) put! @(v 'put!) bump! @(v 'bump!)
        registers @(v 'registers) bindings @(v 'bindings)
        read-local u/read-local call u/call-values! step u/step! resume u/resume!
        layout @(v 'callee-slots) push @(v 'push-frame!) expr @(v 'expr!)
        unbound @(v 'unbound)
        fresh (fn [n values]
                (if (< n threshold) (registers n values)
                  (let [bank (PagedRegisters. (int n) unbound)]
                    (doseq [[id value] values] (.set bank (int id) value))
                    bank)))
        bind! (fn [locals params args]
                (dotimes [i (count params)] (store! locals (nth params i) (nth args i)))
                locals)
        deliver! (fn [s result]
                   (if (.isEmpty ^ArrayDeque (:frames s))
                     (do (put! s 4 :done) (put! s 5 result))
                     (let [frame ^objects (.removeLast ^ArrayDeque (:frames s))
                           locals (aget frame 2)]
                       (store! locals (aget frame 1) result)
                       (put! s 0 (aget frame 0)) (put! s 1 locals) (put! s 2 (aget frame 3)))))
        direct! (fn [s target args dest continuation]
                  (let [name (second target)]
                    (if (or (not= :direct (first target)) (instance? prototype.machine.Builtin name))
                      (do
                        ;; Ordinary closure routing has a dense tail-reuse ABI.
                        ;; Materialize before falling back; joins remain snapshots.
                        (when (paged? (ctl s 1)) (put! s 1 (.toArray ^PagedRegisters (ctl s 1))))
                        (call s target args dest continuation))
                      (do
                        (when continuation (push s continuation dest (ctl s 1) (ctl s 2)))
                        (let [{:keys [params body] :as function} (get (:functions s) name)]
                          (when-not function (m/fail "Unresolved function" {:target name}))
                          (when-not (= (count params) (count args))
                            (m/fail "Guest arity mismatch" {:target name :expected (count params) :actual (count args)}))
                          (let [n (layout s name function)]
                            (put! s 0 body)
                            (if continuation
                              (do (put! s 1 (bind! (fresh n nil) params args)) (put! s 2 (HashMap.)))
                              (let [old (ctl s 1)
                                    locals (if (= (width old) n)
                                             (do (if (paged? old) (.clear ^PagedRegisters old)
                                                   (Arrays/fill ^objects old unbound)) old)
                                             (fresh n nil))]
                                (bind! locals params args)
                                (put! s 1 locals) (.clear ^HashMap (ctl s 2))))))))))]
    (with-redefs-fn
      {(v 'registers) fresh
       (v 'bind-params!) bind!
       (v 'bindings) (fn [locals] (bindings (if (paged? locals) (.toArray ^PagedRegisters locals) locals)))
       #'u/read-local (fn [locals id]
                       (if-not (paged? locals) (read-local locals id)
                         (let [value (.get ^PagedRegisters locals (int id))]
                           (if (identical? value unbound) (m/fail "Unbound variable" {:variable id}) value))))
       #'u/call-values! direct!
       #'u/deliver! deliver!
       #'u/join! (fn [s id params body]
                  (let [locals (ctl s 1)]
                    (u/capture-join! s id params body
                                     (if (paged? locals) (.snapshot ^PagedRegisters locals)
                                       (aclone ^objects locals)))))
       #'u/jump-values! (fn [s id args]
                         (let [join ^objects (.get ^HashMap (ctl s 2) id)]
                           (when-not (and join (= (count (aget join 0)) (count args)))
                             (m/fail "Invalid join" {:join id}))
                           (let [saved (aget join 2)
                                 locals (if (paged? saved) (.fork ^PagedRegisters saved) (aclone ^objects saved))]
                             (bind! locals (aget join 0) args)
                             (put! s 1 locals) (put! s 0 (aget join 1)))))
       #'u/step! (fn [s]
                  (let [locals (ctl s 1) body (ctl s 0)]
                    (if (and (paged? locals) (= :let (nth body 0 nil)))
                      (do
                        (when-not (= :running (ctl s 4))
                          (m/fail "Machine is not running" {:status (ctl s 4)}))
                        (bump! s 2 1)
                        (let [id (int (nth body 1)) value (expr s (nth body 2))]
                          (store! locals id value) (put! s 0 (nth body 3))))
                      (step s))) s)
       #'u/resume! (fn [s value]
                    (if-not (paged? (ctl s 1)) (resume s value)
                      (case (ctl s 4)
                        :suspended (do (store! (ctl s 1) (ctl s 6) value) (put! s 6 nil) (put! s 4 :running))
                        :host-call (do (store! (ctl s 1) (:dest (ctl s 6)) value) (put! s 6 nil) (put! s 4 :running))
                        :paused (put! s 4 :running)
                        (m/fail "State is not resumable" {:status (ctl s 4)}))) s)
       #'u/locals-array (fn [s]
                         (let [locals (ctl s 1)]
                           (if-not (paged? locals) locals
                             (let [dense (.toArray ^PagedRegisters locals)] (put! s 1 dense) dense))))}
      thunk)))

(defn probe [context sizes]
  (let [measure (or (resolve 'prototype.unchanged-program-benchmark/measure)
                    (throw (ex-info "Load research/unchanged-program-benchmark.clj before probing" {})))
        run (get-in context [:workloads :mutable-private])
        modes [:ordinary :adapter-dense :paged-32 :paged-64]
        execute (fn [mode n]
                  (case mode
                    :ordinary (run n)
                    :adapter-dense (with-runtime Long/MAX_VALUE #(run n))
                    :paged-32 (with-runtime 32 #(run n))
                    :paged-64 (with-runtime 64 #(run n))))]
    (doseq [_ (range 8) mode modes] (execute mode 100))
    {:scope "Valid raw RBMap IR; scoped research adapter; private build/fold/final freeze; complete World parity outside timing."
     :runs (vec (for [n sizes
                      :let [expected ((get-in context [:workloads :reference]) n)]
                      trial (range 7)
                      mode (if (even? trial) modes (reverse modes))]
                  (let [[actual metrics] (measure #(execute mode n))]
                    (assert (= expected actual))
                    (assoc metrics :n n :trial trial :mode mode))))}))
