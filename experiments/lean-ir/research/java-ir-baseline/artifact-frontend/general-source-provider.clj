(ns general-frontend-source-provider-v1
  "Independent actual-source/gate observations. Admission checks borrow guest
   roots and never advance, retain, release, reply or install a Program. Opening
   explicitly runs the existing idle original-options/module proofs."
  (:require [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [filesystem-nat-source-provider-v2 :as finite]
            [heartbeat-lab-options-proof :as options-proof]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.node-decoder-v1 :as decoder]
            [artifact-declaration-authority-v4 :as authority])
  (:import [java.util WeakHashMap IdentityHashMap] [java.lang.reflect InvocationTargetException]))

(deftype Provider [])
(deftype GateReceipt [])
(defonce ^:private providers (WeakHashMap.))
(defonce ^:private gates (WeakHashMap.))
(def main-label "ObservedFrontendCommand.processCommandObserved")
(def gate-label "ObservedFrontendCommand.beforeElaboration")
(def main-sha "17983ef01b12b3e0ba4b896fa62950541f48cb64e5d8dcca46bededeacc9dcb8")
(def gate-sha "bf96d5878e30e9e49eaf2b451742599e044afaaaea7f16423a9653fe6f49ecb9")
(defn- need [ok text] (when-not ok (throw (ex-info text {:profile :general-frontend-source-provider-v1}))))
(defn- field [x n] (.get (doto (.getDeclaredField (class x) n) (.setAccessible true)) x))
(defn- guard [s method value]
  (try (.invoke (doto (.getDeclaredMethod (class (sp/engine s)) method (into-array Class [Object])) (.setAccessible true))
                (sp/engine s) (object-array [value]))
       (catch InvocationTargetException cause (throw (.getCause cause)))))
(defn- registered [table token message]
  (locking table (or (.get ^WeakHashMap table token) (throw (ex-info message {})))))
(defn- state [token] (registered providers token "Actual open source Provider required"))
(defn- same-issuer? [p entry]
  (and (some? (:issuer p)) (identical? (:issuer p) (:issuer entry))))
(defn- ctor [s x tag n bytes] (#'finite/ctor s x tag n bytes))
(defn- array-values [s x] (#'finite/array-values s x))
(defn- frozen [s x] (#'finite/frozen-data s x))
(defn- nat [x maximum]
  (need (and (instance? Long x) (<= 0 x maximum)) "Bounded exact guest Nat required") x)
(defn- hash-text [text] (#'finite/sha text))
(defn- stamp [s]
  (let [e (sp/engine s)]
    {:counts (mapv #(field e %) ["instructions" "allocations" "stores" "retains" "releases" "shellDeletes"])
     :roots (mapv #(field e %) ["program" "pc" "hostRequest" "codeRequest" "runtimeAction"])
     :flags (mapv #(field e %) ["closed" "disposed" "untrackedFailure" "advancing"])}))
(defn- readonly [p f]
  (let [s (:frontend p) before (stamp s)]
    (try (f)
         (finally
           (let [after (stamp s)]
             (need (and (= (:counts before) (:counts after)) (= (:flags before) (:flags after))
                        (every? true? (map identical? (:roots before) (:roots after))))
                   "Source observer advanced/mutated the guest"))))))

(defn- capture-source [captured]
  (let [text (:text captured) path (:path captured) module (:module captured)]
    (need (and (string? text) (instance? java.nio.file.Path path) (vector? module) (<= 1 (count module) 128)
               (every? #(and (string? %) (<= 1 (count %) 4096)
                             (not-any? #{\. \/ \\ \u0000} %)) module)) "Bounded captured source/module/path required")
    (let [bytes (.getBytes ^String text "UTF-8") end (alength bytes)]
      (need (and (<= end 65536) (= text (String. bytes java.nio.charset.StandardCharsets/UTF_8)) (= end (:byte-count captured)) (= (hash-text text) (:sha256 captured)))
            "Captured immutable UTF-8 extent/digest differs")
      {:text text :filename (str path) :module module :sha256 (:sha256 captured) :byte-count end
       :boundaries (conj (into #{} (keep-indexed (fn [i b] (when (not= 128 (bit-and 192 b)) i))) bytes) end)
       :line-starts (conj (into [0] (keep-indexed (fn [i b] (when (= 10 (bit-and 255 b)) (inc i)))) bytes) end)})))
(defn- position! [p x]
  (nat x (get-in p [:capture :byte-count]))
  (need (contains? (get-in p [:capture :boundaries]) x) "Position splits a captured UTF-8 code point") x)
(defn- input! [p]
  (let [s (:frontend p) {:keys [text filename byte-count line-starts]} (:capture p)
        f (ctor s (:input p) 0 4 0) ff (ctor s (:file-map p) 0 2 0)]
    (need (and (= text (aget ^objects f 0)) (= filename (aget ^objects f 1))
               (= byte-count (aget ^objects f 3)) (identical? (:file-map p) (aget ^objects f 2))
               (= text (aget ^objects ff 0)) (= line-starts (array-values s (aget ^objects ff 1))))
          "Actual InputContext/FileMap bytes/name/UTF-8 lines differ")))
(defn- scope-view [p command]
  (let [s (:frontend p) cf (ctor s command 0 11 0)]
    (need (= 0 (aget ^objects cf 5)) "Protected cached command maxRecDepth changed")
    (loop [tail (aget ^objects cf 2) n 0 top nil]
      (if (= 0 tail)
        (do (need top "Missing command scope") (assoc top :environment (aget ^objects cf 0)))
        (let [_ (need (< n 128) "Scope depth bound")
              pair (ctor s tail 1 2 0) sf (ctor s (aget ^objects pair 0) 0 10 3)
              flags (mapv #(Byte/toUnsignedInt %) (sp/scalars s (aget ^objects pair 0)))
              opts (aget ^objects sf 1)]
          (need (and (string? (aget ^objects sf 0)) (<= (count (aget ^objects sf 0)) 4096)
                     (every? #(= 0 (aget ^objects sf %)) [3 4 7 8 9])
                     (every? empty? (map #(array-values s (aget ^objects sf %)) [5 6]))
                     (contains? #{0 1} (first flags)) (= [0 0] (subvec flags 1))
                     (= (:frozen-options p) (frozen s opts)))
                "Scope options/binders/attributes/meta/public state outside policy")
          (frozen s (aget ^objects sf 2))
          (recur (aget ^objects pair 1) (inc n) (or top {:options opts :scope (aget ^objects pair 0)})))))))
(defn- state-view [p root]
  (let [s (:frontend p) f (ctor s root 0 4 0) ps (aget ^objects f 1) pf (ctor s ps 0 1 2)
        flags (mapv #(Byte/toUnsignedInt %) (sp/scalars s ps))]
    (need (= [0 0] flags) "Recovering/leading parser state outside successful profile")
    (merge (scope-view p (aget ^objects f 0))
           {:state root :command-state (aget ^objects f 0) :messages (aget ^objects (ctor s (aget ^objects f 0) 0 11 0) 1) :parser-state ps
            :pos (position! p (aget ^objects pf 0)) :cmd-pos (position! p (aget ^objects f 2))
            :commands (array-values s (aget ^objects f 3))})))
(defn- current-view [p]
  (let [s (:frontend p) ref (guard s "reference" (:state-ref p))]
    (state-view p (aget ^objects (sp/fields s ref) 0))))
(defn- authenticate! [p header]
  (source/guard-source! (:code-receipt p) (:source p))
  (let [name (j/lean-name-data (j/request-value header "name")) entry (source/lookup-entry (:code-receipt p) name)]
    (need entry "Header outside actual accepted source")
    (source/authenticate-canonical-header! (:source p) (:row entry) (:sha256 entry) header)))
(defn- main-module! [p environment]
  (need (identical? (:name (:module-proof p))
                   (#'finite/actual-main-module (:frontend p) (:layout (:module-proof p)) environment))
        "Actual main module differs from captured source"))
(defn- check! [p]
  (let [s (:frontend p) e (sp/engine s) d (:driver s)]
    (source/guard-source! (:code-receipt p) (:source p))
    (need (and (identical? (:thread p) (Thread/currentThread))
               (identical? e (:engine p)) (identical? (:program (sp/ctx s)) (field e "program"))
               (identical? (:source p) (:source d))
               (identical? (:input p) (sp/owned s :input)) (identical? (:state-ref p) (sp/owned s :state-ref))
               (identical? (:old-owner p) (sp/owned s (:old-owner-key p)))
               (not-any? true? (map #(field e %) ["closed" "disposed" "untrackedFailure" "advancing"])))
          "Source/engine/owner/thread lease differs")
    (ctor s (:old-owner p) 0 4 0)
    (guard s "reference" (:state-ref p))
    (input! p)
    (need (= (:frozen-options p) (frozen s (:options p))) "Initial protected options mutated")
    (need (= (:frozen-name (:module-proof p)) (frozen s (:name (:module-proof p)))) "Module Name mutated")
    (let [id (:compiler-ref-id p) ready ^booleans (field e "constantReady") retired ^booleans (field e "constantRetired")
          provenance (.get ^java.util.Map (field e "preparedGlobalSources") (int id))
          compiler-ref (:compiler-ref p) compiler (:compiler p) target (:compiler-target p)]
      (need (and (aget ready id) (not (aget retired id))
                 (identical? compiler-ref (aget ^objects (field e "constants") id))
                 provenance (identical? (:source p) (field provenance "binding"))
                 (identical? compiler (aget ^objects (sp/fields s (guard s "reference" compiler-ref)) 0))
                 (identical? target (field (field compiler "closure") "header"))
                 (zero? (alength ^objects (sp/fields s compiler)))) "Original compiler reference/callback changed")
      (.invoke ^java.lang.reflect.Method (:accepts p) e (object-array [compiler])))
    nil))

(defn- kind-name [leaf] (sp/typed-name (str "Lean.Parser.Command." leaf)))
(def ^:private root-kinds
  (into {} (map (fn [[leaf value]] [(kind-name leaf) value]))
        [["declaration" :command] ["namespace" :command] ["section" :command] ["end" :command]
         ["eoi" :eoi] ["exit" :exit] ["import" :import]]))
(def ^:private declaration-kinds (set (map kind-name ["definition" "theorem" "axiom"])))
(def ^:private forbidden-kinds
  (set (map sp/typed-name
        ["Lean.Parser.Command.set_option" "Lean.Parser.Term.set_option" "Lean.Parser.Tactic.set_option"
         "Lean.Parser.Command.unlock_limits" "Lean.Parser.Command.initialize" "Lean.Parser.Command.builtin_initialize"
         "Lean.Parser.Term.attributes" "Lean.Parser.Command.attribute" "Lean.Parser.Term.attrInstance"
         "Lean.Parser.Command.meta" "Lean.Parser.Command.unsafe" "Lean.Parser.Command.partial"
         "Lean.Parser.Command.public" "Lean.Parser.Command.protected"
         "Lean.Parser.Command.runCmd" "Lean.Parser.Command.runElab" "Lean.Parser.Command.runMeta"
         "Lean.Parser.Tactic.runTac" "Lean.Parser.Command.eval" "Lean.Parser.Command.evalBang"
         "Lean.Parser.Command.withExporting" "Lean.Parser.Command.withWeakNamespace"])))
(defn- raw-substring! [p x]
  (let [f (ctor (:frontend p) x 0 3 0) a (position! p (aget ^objects f 1)) b (position! p (aget ^objects f 2))]
    (need (and (= (get-in p [:capture :text]) (aget ^objects f 0)) (<= a b)) "Syntax substring is outside captured source")))
(defn- source-info! [p x]
  (if (= 2 x) nil
    (let [s (:frontend p) _ (guard s "constructorNode" x) tag (.getInt ^java.lang.reflect.Field (:tag (sp/ctx s)) x)]
      (case tag
        0 (let [f (ctor s x 0 4 0) a (position! p (aget ^objects f 1)) b (position! p (aget ^objects f 3))]
            (need (<= a b) "Reversed Syntax source range")
            (raw-substring! p (aget ^objects f 0)) (raw-substring! p (aget ^objects f 2)))
        1 (let [f (ctor s x 1 2 1) a (position! p (aget ^objects f 0)) b (position! p (aget ^objects f 1))]
            (need (and (<= a b) (contains? #{0 1} (Byte/toUnsignedInt (aget ^bytes (sp/scalars s x) 0))))
                  "Malformed synthetic Syntax range"))
        (need false "Unknown Syntax SourceInfo constructor")))))
(defn- syntax-policy! [p root]
  (let [s (:frontend p) scope (decoder/open-decoder (sp/ctx s) (sp/engine s)
                {:deadline-nanos (+ (System/nanoTime) 5000000000)
                 :max-nodes 16384 :max-visits 100000 :max-depth 256 :max-array 16384
                 :max-edges 100000 :max-chars 262144 :max-output 65536})
        name! (fn [x] ((:project scope) :name x))
        syntax-node (fn [x]
                      (need (not= 0 x) "Syntax.missing is outside successful command policy")
                      (guard s "constructorNode" x)
                      (let [tag (.getInt ^java.lang.reflect.Field (:tag (sp/ctx s)) x)]
                        (case tag
                          1 (let [f (ctor s x 1 3 0)]
                              (source-info! p (aget ^objects f 0))
                              {:kind (name! (aget ^objects f 1)) :args (array-values s (aget ^objects f 2))})
                          2 (let [f (ctor s x 2 2 0)]
                              (source-info! p (aget ^objects f 0))
                              (need (and (string? (aget ^objects f 1)) (<= (count (aget ^objects f 1)) 65536)) "Syntax atom bound")
                              {:args []})
                          3 (let [f (ctor s x 3 4 0)]
                              (source-info! p (aget ^objects f 0)) (raw-substring! p (aget ^objects f 1))
                              (name! (aget ^objects f 2))
                              (need (= 0 (aget ^objects f 3)) "Preresolved/custom parsed identifier outside policy")
                              {:args []})
                          (need false "Unknown Syntax constructor"))))]
    (try
      (let [first-node (syntax-node root) root-kind (:kind first-node) kind (get root-kinds root-kind)
            _ (need kind "Custom or effectful command root is not admitted")
            _ (when (= root-kind (kind-name "declaration"))
                (let [args (:args first-node)]
                  (need (and (= 2 (count args)) (contains? declaration-kinds (:kind (syntax-node (second args)))))
                        "Declaration syntax is outside safe definition/theorem/axiom policy")))
            seen (IdentityHashMap.) active (IdentityHashMap.)]
        (loop [todo [[:enter root 0]] visits 0 count-nodes 0]
          (need (< visits 65536) "Syntax traversal visit bound")
          (if (empty? todo)
            {:kind kind :root-kind root-kind :syntax-nodes count-nodes}
            (let [[op x depth] (peek todo) tail (pop todo)]
              (if (= :leave op)
                (do (.remove active x) (recur tail (inc visits) count-nodes))
                (do
                  (need (<= depth 256) "Syntax depth bound")
                  (need (not (.containsKey active x)) "Cyclic Syntax graph")
                  (if (.containsKey seen x) (recur tail (inc visits) count-nodes)
                    (let [{:keys [kind args]} (syntax-node x)]
                      (need (not (contains? forbidden-kinds kind)) "Protected option/attribute/meta/effect syntax is forbidden")
                      ;; sectionHeader spells public/meta/@[expose] as atoms,
                      ;; unlike named declaration modifiers. Permit only its
                      ;; empty optional nodes, not token-based text matching.
                      (when (= kind (kind-name "sectionHeader"))
                        (need (every? (fn [arg]
                                        (let [option (syntax-node arg)]
                                          (and (= (sp/typed-name "null") (:kind option)) (empty? (:args option))))) args)
                              "Section modifiers are outside this scope policy"))
                      (need (< count-nodes 16384) "Syntax node bound")
                      (.put seen x true) (.put active x true)
                      (recur (into (conj tail [:leave x depth]) (map #(vector :enter % (inc depth)) (rseq args)))
                             (inc visits) (inc count-nodes))))))))))
      (finally ((:close! scope))))))

(defn- gate-site! [p request]
  (let [s (:frontend p) e (:engine p) ctx (sp/ctx s) program (:program ctx)
        call (field request "call") function (field call "function") header (field function "header")
        active (field e "active") active-header (field active "header")
        prepared (aget ^objects (field program "preparedBodies") (int (field active "id")))]
    (need (and (identical? request (j/host-request ctx e)) (identical? program (field e "program"))
               (identical? (field request "owner") (field e "runtimeIdentity"))
               (identical? header (:gate-header p)) (identical? active-header (:main-header p))
               (identical? active (aget ^objects (field program "functions") (int (field active "id"))))
               prepared (identical? prepared (field e "activePrepared"))
               ;; HostCall destinations are physical stack slots; the
               ;; authenticated prepared Body below keeps the SSA index41.
               (= (+ (field e "bp") 41) (field call "dest")) (false? (field call "facade"))
               (identical? (field call "next") (field e "pc"))
               (= "ansatz_observed_frontend_gate_v1" (.symbol request))
               (= ["object" "object" "tobject" "object" "object" "void"] (vec (.paramTypes request)))
               (= [true true true true true false] (vec (.borrowed request)))
               (= "tagged" (.resultType request))) "Spurious/foreign source gate request or caller")
    (authenticate! p header) (authenticate! p active-header)
    (loop [todo [(field prepared "body")] seen (IdentityHashMap.) matches []]
      (need (< (.size seen) 4096) "Compiled gate call-site bound")
      (if (empty? todo)
        (do (need (and (= 1 (count matches)) (identical? (field (first matches) "next") (field call "next")))
                  "Gate is not at the unique canonical companion FAP site") nil)
        (let [b (peek todo) tail (pop todo)]
          (if (or (nil? b) (.containsKey seen b)) (recur tail seen matches)
            (let [_ (.put seen b true) expr (field b "expr")
                  found (and (= 0 (field b "op")) expr (= 3 (field expr "op")) (identical? function (field expr "target")))
                  _ (when found
                      (let [prefix (field b "next") next (field prefix "next")
                            ne (field next "expr") target (when ne (field ne "target"))]
                        ;; Exactly the source-produced inc Syntax24 by one.
                        ;; Physical Body omits the raw true/false RC hints;
                        ;; those remain fixed by authenticated main row17983.
                        (need (and (= 41 (field b "a")) (= [1 4 24 25 26 0] (vec (field expr "args")))
                                   (= 4 (field prefix "op")) (= 24 (field prefix "a")) (= 1 (field prefix "b"))
                                   (= 0 (field next "op")) (= 42 (field next "a")) ne (= 3 (field ne "op"))
                                   target (= (sp/typed-name "Lean.Elab.Frontend.elabCommandAtFrontend")
                                             (j/lean-name-data (j/request-value (field target "header") "name")))
                                   (= [24 1 2 0] (vec (field ne "args")))) "Compiled gate successor differs")
                        (authenticate! p (field target "header"))))
                  children (concat [(field b "next") (field b "body")] (seq (field b "alternatives")))]
              (recur (into tail children) seen (cond-> matches found (conj b))))))))))

(defn open-provider!
  "Explicit idle preparation: genuine original option/main-module proofs may
   call guest helpers and use the existing frontend ownership journal. Returned
   callbacks thereafter are read-only. No boolean caller proof is accepted."
  [child frontend captured-source {:keys [layout-directory]}]
  (need (and (string? layout-directory) (seq layout-directory)) "Explicit compiled layout directory required")
  (let [capture (capture-source captured-source) s frontend d (:driver s) e (sp/engine s) src (:source d)
        code (:code-receipt child)
        _ (need (and (identical? e (get-in child [:driver :engine]))
                     (identical? src (get-in child [:driver :source]))
                     (identical? (:current-ctx d) (get-in child [:driver :current-ctx])))
                "Provider requires this actual child frontend/Source")
        _ (source/guard-source! code src)
        proof (options-proof/check-prepared! s)
        _ (need (and (= :lab-options-proved (:status proof)) (identical? s (:session proof))) "Original idle options proof failed")
        input (sp/owned s :input) inf (ctor s input 0 4 0)
        initial (#'finite/current-view s) opts (:options initial)
        key (:state-owner-key (first @(:observations s))) old (sp/owned s key)
        base {:frontend s :engine e :source src :code-receipt code :thread (Thread/currentThread)
              :input input :file-map (aget ^objects inf 2) :state-ref (sp/owned s :state-ref)
              :old-owner-key key :old-owner old :options opts :frozen-options (frozen s opts)
              :capture capture :active (atom nil) :issuer (Object.)}
        auth (fn [h] (authenticate! base h))
        header-for (fn [label] ((sp/host-helper "ensure-header!") d (sp/typed-name label)))
        module-proof (#'finite/prove-main-module! s capture auth header-for layout-directory)
        ref-header (header-for "Lean.compileDeclsRef") _ (auth ref-header)
        _ (need (= finite/compiler-ref-sha (j/request-value ref-header "originalSha256")) "Compiler ref source differs")
        ref-id (j/function-id (sp/ctx s) "Lean.compileDeclsRef")
        compiler-ref (aget ^objects (field e "constants") ref-id)
        compiler (aget ^objects (sp/fields s (guard s "reference" compiler-ref)) 0)
        target (field (field compiler "closure") "header")
        _ (auth target)
        _ (need (and (= finite/compiler-target-sha (j/request-value target "originalSha256"))
                     (identical? target (header-for "Lean.Compiler.LCNF.main._boxed"))) "Original compiler callback differs")
        main (header-for main-label) gate (header-for gate-label)
        _ (doseq [[h pin] [[main main-sha] [gate gate-sha]]]
            (auth h) (need (= pin (j/request-value h "originalSha256")) "Companion source row pin differs"))
        accepts (doto (.getDeclaredMethod (class e) "acceptsClosure" (into-array Class [(:node-class (sp/ctx s))])) (.setAccessible true))
        p (assoc base :module-proof module-proof :compiler-ref-id ref-id :compiler-ref compiler-ref
                     :compiler compiler :compiler-target target :accepts accepts :main-header main :gate-header gate)
        token (Provider.)]
    (readonly p #(do (check! p) (let [v (current-view p)] (main-module! p (:environment v)))))
    (locking providers (.put providers token p)) token))

(defn callbacks
  "Definition-only trusted callbacks for the generic CommandReceipt controller.
   Returned borrowed views carry no guest owners or standalone admission power."
  [provider]
  (state provider)
  (letfn [(borrow [f] (let [p (state provider)] (readonly p #(do (check! p) (f p)))))
          (capture! [p request]
            (need (or (nil? @(:active p)) (= :observed (:stage @(:active p)))) "Prior source command is still active/failed")
            (let [s (:frontend p) v (current-view p)]
              (need (and (identical? (:engine p) (:engine request)) (identical? (:source p) (:source request))
                         (identical? (:input p) (:input request)) (identical? (:state-ref p) (:state-ref request)))
                    "Foreign command capture roots")
              (main-module! p (:environment v))
              (let [capture {:engine (:engine p) :source (:source p) :input (:input p) :state-ref (:state-ref p)
                             :before-state (:state v) :start-pos (:pos v) :commands (:commands v)
                             :description {:profile :observed-classic-prelude-command-v1
                                           :input-sha256 (get-in p [:capture :sha256])
                                           :filename (get-in p [:capture :filename]) :module (get-in p [:capture :module])
                                           :utf8-bytes (get-in p [:capture :byte-count]) :command-start (:pos v)
                                           :command-index (count (:commands v)) :companion-main-sha main-sha :gate-sha gate-sha
                                           :compiler-ref-sha finite/compiler-ref-sha :compiler-target-sha finite/compiler-target-sha}}]
                (reset! (:active p) {:capture capture :stage :captured}) capture)))
          (gate! [p {:keys [engine source request arguments initial-observation capture]}]
            (let [s (:frontend p) active @(:active p)]
              (need (and (= :captured (:stage active)) (identical? capture (:capture active))
                         (identical? engine (:engine p)) (identical? source (:source p))) "Gate capture/source binding differs")
              (gate-site! p request)
              (let [actual (vec (.arguments request)) args (vec arguments)]
                (need (and (= 6 (count actual)) (= 5 (count args)) (= 0 (nth actual 5))
                           (every? true? (map identical? args (take 5 actual)))) "Gate semantic borrowed arguments differ")
                (let [[input before syntax parsed messages] args
                      prior (state-view p before) current (current-view p)
                      pf (ctor s parsed 0 1 2) end (position! p (aget ^objects pf 0))
                      _ (need (= [0 0] (mapv #(Byte/toUnsignedInt %) (sp/scalars s parsed))) "Parser recovery/leading flags outside policy")
                      _ (need (and (identical? input (:input p)) (identical? before (:before-state capture))
                                   (identical? before (:state initial-observation))
                                   (identical? (:command-state prior) (:command-state initial-observation))
                                   (identical? (:environment prior) (:environment initial-observation))
                                   (identical? (:messages prior) (:messages initial-observation))
                                   (= (:start-pos capture) (:pos prior))
                                   (<= (:pos prior) end)
                                   (identical? parsed (:parser-state current))
                                   (= (:pos prior) (:cmd-pos current))
                                   (= end (:pos current))
                                   (identical? messages (aget ^objects (ctor s (:command-state current) 0 11 0) 1))
                                   (= (inc (count (:commands capture))) (count (:commands current)))
                                   (every? true? (map identical? (:commands capture) (pop (:commands current))))
                                   (identical? syntax (peek (:commands current)))) "Actual parse occurrence/state/log/source span differs")
                      policy (syntax-policy! p syntax)
                      _ (need (or (not= :command (:kind policy)) (< (:pos prior) end)) "Nonterminal parser did not advance")
                      _ (when (= :eoi (:kind policy))
                          (need (= end (get-in p [:capture :byte-count])) "eoi is not at captured UTF-8 end"))
                      token (GateReceipt.) entry {:issuer (:issuer p) :capture capture :request request :arguments args
                                                 :policy policy :start (:pos prior) :end end}]
                  (main-module! p (:environment current))
                  (locking gates (.put gates token entry))
                  (reset! (:active p) {:capture capture :stage :gated :gate token}) token))))
          (observed! [p {:keys [engine source result result-wrapper gate-receipt arguments initial-observation final-observation capture]}]
            (let [s (:frontend p) g (registered gates gate-receipt "Actual source GateReceipt required") active @(:active p)]
              (need (and (same-issuer? p g) (identical? capture (:capture g))
                         (identical? gate-receipt (:gate active)) (= :gated (:stage active))
                         (identical? engine (:engine p)) (identical? source (:source p))
                         (every? true? (map identical? (:arguments g) arguments)) (= 5 (count arguments)))
                    "Observed result has foreign/replayed gate custody")
              (let [wrapper-fields (ctor s result-wrapper 0 1 0)
                    _ (need (identical? result (aget ^objects wrapper-fields 0)) "Observation is not the actual owned IO success payload")
                    f (ctor s result 0 8 4) [input before syntax parsed parse-log] (:arguments g)
                    flags (mapv #(Byte/toUnsignedInt %) (sp/scalars s result)) kind (get-in g [:policy :kind])
                    after (state-view p (:state final-observation))
                    expected [(if (= :command kind) 0 1) (if (= :eoi kind) 1 0) (if (= :exit kind) 1 0) (if (= :import kind) 1 0)]
                    view {:kind kind :input input :before-state before :syntax syntax :parser-state parsed
                          :parser-messages parse-log :elaboration-messages (aget ^objects f 5)
                          :start-pos (aget ^objects f 6) :end-pos (aget ^objects f 7)}]
                (need (and (= expected flags)
                           (every? true? (map identical? [input before syntax parsed parse-log] (take 5 (vec f))))
                           (identical? before (:state initial-observation))
                           (identical? (:command-state after) (:command-state final-observation))
                           (identical? (:environment after) (:environment final-observation))
                           (identical? (aget ^objects f 5) (:messages final-observation))
                           (identical? (:messages after) (:messages final-observation))
                           (identical? parsed (:parser-state after))
                           (= [(:start g) (:end g)] [(position! p (:start-pos view)) (position! p (:end-pos view))])
                           (= (:end g) (:pos after)) (identical? syntax (peek (:commands after))))
                      "Returned Observation differs from actual parser/elaboration roots")
                (main-module! p (:environment after))
                (reset! (:active p) (assoc active :stage :observed)) view)))
          (inspect! [p {:keys [observation stage]}]
            (let [v (state-view p (:state observation))]
              (need (and (contains? #{:baseline :observed} stage)
                         (identical? (:command-state v) (:command-state observation))
                         (identical? (:environment v) (:environment observation))
                         (identical? (:messages v) (:messages observation))) "Foreign frontend observation roots")
              (main-module! p (:environment v))))]
    {:check! (fn [_] (borrow (constantly nil)))
     :before-command! (fn [request] (borrow #(capture! % request)))
     :before-call! (fn [{:keys [engine source header]}]
                    (borrow #(do (need (and (identical? engine (:engine %)) (identical? source (:source %))) "Foreign source call")
                                 (authenticate! % header))))
     :after-taken! (fn [{:keys [engine source header slot result]}]
                    (borrow #(do (need (and (identical? engine (:engine %)) (identical? source (:source %))
                                                (= :owned (aget ^objects slot 1)) (identical? result (aget ^objects slot 0))) "Foreign taken source result")
                                 (authenticate! % header))))
     :inspect-observation! (fn [request] (borrow #(inspect! % request)))
     :check-gate! (fn [request] (borrow #(gate! % request)))
     :check-observed-result! (fn [request] (borrow #(observed! % request)))}))

(defn close!
  "Drop only private host metadata. This does not release any guest occurrence,
   retire a command, close a Source or grant cleanup of an outstanding request."
  [provider]
  (let [p (state provider)]
    (locking gates
      (let [it (.iterator (.entrySet gates))]
        (while (.hasNext it)
          (when (same-issuer? p (.getValue ^java.util.Map$Entry (.next it))) (.remove it)))))
    (locking providers (.remove providers provider))) nil)
