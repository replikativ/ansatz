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

Returned lists are immutable host values. Returned byte arrays are mutable host
copies. No returned container carries a guest Node or an interpreter ownership
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
