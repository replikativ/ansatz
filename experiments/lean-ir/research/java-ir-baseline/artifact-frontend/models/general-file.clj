(ns general-frontend-file-checks-v1
  "Pure codec/lifecycle/orchestration models. No actual frontend acceptance."
  (:require [clojure.test :refer [deftest is run-tests]]
            [general-frontend-file-v1 :as file]
            [general-command-receipt-v1 :as command]
            [general-generated-batch-v1 :as batch]
            [heartbeat-lab-options-proof :as options])
  (:import [java.math BigInteger] [ansatz.kernel Expr Name]))
(deftest nat-codec-is-exact-immutable-and-bounded
  (doseq [x [0 Long/MAX_VALUE BigInteger/ZERO (.shiftLeft BigInteger/ONE 200)]]
    (is (identical? x (#'file/nat! x))))
  (doseq [x [nil -1 (int 1) 1.0 (Object.) (object-array [0]) (.negate BigInteger/ONE)
             (.shiftLeft BigInteger/ONE 4096) (proxy [BigInteger] ["1"] (signum [] (throw (AssertionError. "must reject subclass before method"))))]]
    (is (thrown? Exception (#'file/nat! x)))))
(deftest typed-names-are-not-display-label-authority
  (is (= (Name/mkStr (Name/mkStr Name/ANONYMOUS_NAME "A") "b")
         (#'file/kernel-name ["str" ["str" ["anonymous"] "A"] "b"])))
  (is (not= (#'file/kernel-name ["str" ["anonymous"] "A.b"])
            (#'file/kernel-name ["str" ["str" ["anonymous"] "A"] "b"])))
  (is (thrown? Exception (#'file/kernel-name ["str" nil "bad"]))))
(deftest nat-type-is-a-kernel-expression-not-a-name-string
  (let [nat (Expr/mkConst (Name/mkStr Name/ANONYMOUS_NAME "Nat") (object-array 0) false)]
    (is (#'file/nat-constant? nat))
    (is (not (#'file/nat-constant? "Nat")))
    (is (not (#'file/nat-constant? (Expr/mkConst (Name/mkStr Name/ANONYMOUS_NAME "Bool") (object-array 0) false))))))
(deftest unissued-file-tokens-and-terminal-metadata-have-no-authority
  (doseq [x [nil {} (file/->FileRun)]]
    (is (thrown? Exception (file/inspect x)))
    (is (thrown? Exception (file/owner-packet x)))
    (is (thrown? Exception (file/load! x)))
    (is (thrown? Exception (file/next-command! x)))
    (is (thrown? Exception (file/invoke-nat! x ["str" ["anonymous"] "f"] 0)))
    (is (thrown? Exception (file/close! x)))))
(defn- model [outcomes f]
  (let [holder (atom {:thread (Thread/currentThread) :status :open :stage :idle :next-command 0
                      :commands [] :entries {} :execution :supported :max-commands 128
                      :bundle {:frontend {} :admission {:adapter {:versions (atom [:actual-version])}}}})
        observed (atom outcomes) events (atom [])]
    (with-redefs-fn {#'file/cell (fn [_] holder) #'file/live! (fn [h] @h)
                    #'file/context (fn [_] {:program :actual-program})
                    #'options/rebase-idle-deadline identity
                    #'command/open-command! (fn [& _] :actual-run)
                    #'command/run-command! (fn [_] (let [x (first @observed)] (swap! observed rest) x))
                    #'batch/prepare-batch! (fn [& _] {:status :empty :row-count 0})
                    #'command/rebase-idle-deadline! (fn [& _] (swap! events conj :rebase))
                    #'command/retire! (fn [_] (swap! events conj :retire))}
      #(f holder events))))
(deftest zero-publication-commands-and-real-eoi-remain-distinct
  (model [{:status :sealed :receipt :actual :summary {:kind :command :publications []}}
          {:status :sealed :receipt :actual :summary {:kind :eoi :publications []}}]
    (fn [holder events]
      (is (= :ready (:status (file/load! :modeled))))
      (is (= 2 (:next-command @holder)))
      (is (= [:command :eoi] (mapv #(get-in % [:command :kind]) (:commands @holder))))
      (is (= [:rebase :retire :rebase :retire] @events))
      (is (= :actual-program (:linked-program @holder)))
      (is (= :actual-version (:checked-version @holder))))))
(deftest exit-and-import-are-stops-not-eof
  (doseq [kind [:exit :import]]
    (model [{:status :sealed :receipt :actual :summary {:kind kind :publications []}}]
      (fn [holder events]
        (is (= :stopped (:status (file/load! :modeled))))
        (is (= kind (:stage @holder)))
        (is (= [:rebase :retire] @events))
        (is (not (contains? @holder :linked-program)))))))
(deftest checked-but-unexecutable-code-is-not-a-checking-failure
  (model [{:status :sealed :receipt :actual :summary {:kind :eoi :publications []}}]
    (fn [holder _]
      (with-redefs [batch/prepare-batch! (fn [& _] {:status :unsupported :reason "unavailable lane"})]
        (is (= :unsupported (:status (file/load! :modeled))))
        (is (= :unsupported (:execution @holder)))
        (is (= :eoi (:stage @holder)))
        (is (nil? (:active @holder)))))))
(deftest failed-command-keeps-actual-run-and-never-retires-or-links
  (model [{:status :failed :failure {:class "actual"}}]
    (fn [holder events]
      (with-redefs [batch/prepare-batch! (fn [& _] (throw (AssertionError. "no batch after failure")))]
        (is (= :failed (:status (file/load! :modeled))))
        (is (= :actual-run (:active @holder)))
        (is (empty? @events))
        (is (thrown? Exception (file/next-command! :modeled)))))))
(deftest command-limit-is-an-explicit-stop-without-opening-another-run
  (model []
    (fn [holder events]
      (swap! holder assoc :next-command 128)
      (with-redefs [command/open-command! (fn [& _] (throw (AssertionError. "no guest start past limit")))]
        (is (= :stopped (:status (file/load! :modeled))))
        (is (= :command-limit (:stage @holder)))
        (is (nil? (:active @holder)))
        (is (empty? @events))))))
(defn check! [] (run-tests 'general-frontend-file-checks-v1))
