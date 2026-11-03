# JVM and Clojure values

Function handles use the admitted Lean signature. A host value selects neither
the signature nor a constructor layout. The examples below assume entries with
the stated supported signatures have already been loaded; they do not add new
entries to a Project.

## Java

For a handle accepting `Option Unit`, these are distinct arguments:

```java
optionUnit.invoke(Optional.empty());                    // none
optionUnit.invoke(Optional.of(LeanUnit.INSTANCE));      // some ()
```

Use `LeanChoice.left(value)` and `LeanChoice.right(value)` for `Sum`. For
`Except`, left carries the error and right carries the successful value. Product
and List payloads use ordinary indexed lists, including inside a branch:

```java
// Input type: Except String (Unit × Option Unit)
Object input = LeanChoice.right(
    List.of(LeanUnit.INSTANCE, Optional.of(LeanUnit.INSTANCE)));
Object result = nestedFunction.invoke(input);
```

For v1/v2 signatures, returned lists are immutable host values and returned byte
arrays are mutable host copies. V3 typed values use the views described below. No returned container carries a guest Node or an interpreter ownership
obligation.

`LeanFunction.invoke(Object...)` takes the exact explicit arity of its handle.
For one `Array Nat` argument supplied as an `Object[]`, prevent Java varargs from
spreading it into several arguments:

```java
Object[] values = {BigInteger.ZERO, BigInteger.TEN};
Object result = arrayFunction.invoke((Object) values);
// An indexed List is also accepted for this Array argument.
```

Multiple explicit arguments are passed separately. There is no implicit
currying, proof synthesis or insertion of implicit arguments.

## Clojure

The wrapper converts supported containers recursively, using the checked child
types. For an admitted identity with input `Option (Option Unit)`:

```clojure
(nested-option nil)                      ; => nil                ; none
(nested-option {:some nil})              ; => {:some nil}        ; some none
(nested-option {:some {:some nil}})      ; => {:some {:some nil}} ; some (some ())
```

For `Except String (Unit × Option Unit)`, use `{:error "message"}` or
`{:ok [nil {:some nil}]}`. For `Sum`, the corresponding keys are `:left` and
`:right`. Each branch map has exactly one key. These tags preserve the nested
meaning of `nil`: Unit and Option are interpreted according to their descriptors.

Java carriers can be mixed with Clojure containers. For example, a supplied
`LeanChoice/right` payload receives the same recursive Unit, Option and Product
conversion as an `:ok` map:

```clojure
(import '[ansatz.lean.jvm LeanChoice])
(nested-except (LeanChoice/right [nil {:some nil}]))
;; An identity entry of the type above returns {:ok [nil {:some nil}]}.
```

Use vectors for Product, List and Array inputs; lazy sequences are refused.
`Float32` expects `(float 1.5)`, while `Float` expects a Double such as `1.5`.
Char uses an integer Unicode scalar code point, including supplementary
characters, rather than a Java Character. Machine integers are range checked.
All conversions have the [documented aggregate and depth bounds](README.md).

An admitted function has one fixed explicit arity. The Clojure IFn accepts that
many positional arguments; a vector is one container argument, not an argument
list to spread automatically. Use `apply` when spreading arguments is intended.

For an `IO α` function, Java returns `IOResult` and Clojure returns
`{:value value :stdout text :stderr text}`. An `Except` inside that value remains
ordinary tagged data. An outer `IO.error` instead fails the call with
`GuestIOError`; an `Except.error` is not converted into that failure.

## Automatic datatype values (v3)

These examples use the three-file [datatype application](examples/datatypes/README.md)
with root `Main`, selecting `DatatypeExample.sample`, `eval`, `simplify`,
`summarize`, `readStats` and `ioEcho` by their fully qualified names. Source
preparation needs the reviewed [v3 producer](producer/README.md#datatype-v3-producer). A v3 prepared artifact subsequently needs only the JVM SDK.

Java receives native-derived metadata and immutable values:

```java
LeanFunction sample = project.function("DatatypeExample.sample");
LeanFunction eval = project.function("DatatypeExample.eval");
LeanData tree = (LeanData) sample.invoke(BigInteger.valueOf(11));
System.out.println(eval.invoke(tree));                  // 33
LeanType treeType = eval.argumentTypes().get(0);
LeanName literalName = LeanName.str(
    LeanName.str(LeanName.str(LeanName.anonymous(), "DatatypeExample"), "Tree"),
    "literal");
LeanData literal = treeType.constructor(literalName)
    .create(List.of(BigInteger.valueOf(7)));
System.out.println(eval.invoke(literal));               // 7
LeanData simplified = (LeanData) project.call("DatatypeExample.simplify", tree);
System.out.println(simplified.constructor().name());    // structured name of Tree.literal
System.out.println(simplified.field(0));                // 33
IOResult<?> echo = (IOResult<?>) project.call("DatatypeExample.ioEcho", tree);
System.out.print(echo.stdout());                        // value=33 followed by newline
Object ordinary = treeType.materialize(tree);          // explicit collection snapshot
```

`treeType.constructors()` and each constructor's `fields()` describe constructor
membership, ordered field types and structural Names. They derive from native
evidence; the example's name lookup selects a known constructor without defining
its schema. Use `hasTypeMetadata()` before accessing v3 metadata on a handle of
unknown cohort. Legacy metadata accessors throw `UnsupportedSignature`.

Clojure function metadata contains those same detached type objects. Returned
values support ordinary lookup, destructuring, sequence access and collection
equality without eagerly rebuilding their full payload:

```clojure
(require '[ansatz.lean.jvm :as lean])
(def sample (lean/function project "DatatypeExample.sample"))
(def evaluate (lean/function project "DatatypeExample.eval"))
(def tree (sample 11))
(evaluate tree)                                         ; => 33
(def simplified (lean/call project "DatatypeExample.simplify" tree))
(:lean/fields simplified)                               ; indexed view containing 33
(def literal-name (:lean/constructor simplified))
(def literal {:lean/type (:lean/type simplified)
              :lean/constructor literal-name
              :lean/fields [7]})
(evaluate literal)                                      ; => 7
(def tree-type (first (:lean/argument-types (meta evaluate))))
(lean/call project "DatatypeExample.ioEcho" tree)
;; => {:value tree-view :stdout "value=33\n" :stderr ""}
(def ordinary (lean/materialize tree))                  ; explicit maps/vectors copy
(evaluate ordinary)                                    ; => 33
```

`:lean/type` is a `LeanTypeId`; constructor Names are `LeanName` objects, not
interned application keywords. An edited map becomes an ordinary host value and
is fully validated when passed back. An unchanged genuine view reuses its
certified storage. V3 nested bytes use immutable `LeanBytes`; materialization
creates fresh mutable byte arrays. Legacy v1/v2 byte-copy conventions do not
change. Detached values survive close; a new Project accepts them only when its
logical, defining-product, representation and runtime-class identities match.
