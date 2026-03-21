;; Ansatz kernel for Clojure — Lean-compatible hierarchical names.
;; Thin wrapper over Java Name class for interned identity comparison.

(ns ansatz.kernel.name
  "Hierarchical names matching Lean's Name type.
   Uses Java Name class with intern table for identity-based comparison.
   Name.anonymous is represented as Name/ANONYMOUS_NAME.
   Name.str as Name/mkStr.
   Name.num as Name/mkNum."
  (:import [ansatz.kernel Name]))

(defn anonymous [] Name/ANONYMOUS_NAME)

(defn mk-str
  "Create a Name.str: parent.s"
  [parent s]
  (Name/mkStr parent s))

(defn mk-num
  "Create a Name.num: parent.n"
  [parent n]
  (Name/mkNum parent (long n)))

(defn anonymous? [^Name n] (or (nil? n) (.isAnonymous n)))

(defn str-name? [^Name n] (and (some? n) (.isStr n)))
(defn num-name? [^Name n] (and (some? n) (.isNum n)))

(defn name-prefix ^Name [^Name n]
  (when (some? n) (.prefix n)))

(defn name-component [^Name n]
  (when (some? n)
    (case (.tag n)
      1 (.str n)    ;; STR
      2 (.num n)    ;; NUM
      nil)))

(defn ->string
  "Convert a Name to its dot-separated string representation."
  [^Name n]
  (if (or (nil? n) (.isAnonymous n))
    "[anonymous]"
    (.toString n)))

(defn from-string
  "Parse a dot-separated string into a Name."
  [s]
  (Name/fromString s))
