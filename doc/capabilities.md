# Capabilities

## What is a capability?

In the general sense, a **capability** is an unforgeable token provided with
an API by the system. A file descriptor in UNIX is a classic example of a
capability: only the kernel can produce them, and only certain things can be
done with them. In this way, capabilities allow a system to grant
functionality to users for specific use cases.

## Pact capabilities

A Pact capability is a little different from the general concept: there is no
token that is passed around, instead it is tracked by the evaluator; and the
only thing that can be done with a capability is to ask `require-capability`
if it had been granted or not.

Put very simply, there are three aspects to using capabilities:

1. Use `defcap CAP ARGS` to define a capability, along with a predicate that
   determines when it should be granted. This predicate can refer to the
   arguments provided, the module's data tables, or both.

2. Use `with-capability (CAP ARGS...) EXPR` to grant the capability identified
   by `CAP ARGS...`, provided the capability predicate passes with those
   arguments.

3. Use `require-capability (CAP ARGS...)` to ensure that somewhere earlier in
   the call stack, `with-capability` had granted `CAP ARGS...`.

Although basic, this simple model allows us to implement the concept of
"domain private functions": functions that may only be called by other
functions if certain conditions have been met. Here's a quick example, where
the functions `foo` and `bar` can only be called by `entry`, and only if
certain conditions have been met:
```lisp
(defcap FOO_CALLABLE (value:integer)
  (enforce (> value 0) "Value must be greater than zero"))

(defcap BAR_CALLABLE (value:integer)
  (enforce (< value 0) "Value must be less than zero"))

(defun entry (value:integer)
  (if (> value 0)
      (with-capability (FOO_CALLABLE value)
        (foo value))
      (if (< value 0)
          (with-capability (BAR_CALLABLE value)
            (bar value))
          (print "entry ignoring a zero value"))))

(defun foo (value:integer)
  "Foo never deals with negative numbers or zero."
  (require-capability (FOO_CALLABLE value))
  (print value))

(defun bar (value:integer)
  "Bar never deals with positive numbers or zero."
  (require-capability (BAR_CALLABLE value))
  (print value))
```

This example is a bit contrived, but note a few attributes of this code:

- Neither `foo` or `bar` can ever be called directly, but only through calling
  `entry`.

- `entry` cannot never call `foo` and `bar` with invalid values, as defined by
  the associated capabilities.

- For a given value, `entry` can call either `foo` or `bar`, but never both.

From this it can be seen that Pact capabilities allow for flexible access
control based on user-provided arguments, or data read from the database.

## `defcap`

Defining a Pact capability requires four elements:

1. A name.
2. Arguments that will be passed for every reference to that capability.
3. A predicate that determines when the capability should be granted via
   `with-capability`.
4. Whether other capabilities should be granted along with this capability,
   using `compose-capability`.

Below is an example definition. Note how it uses both the capability argument,
and access to the module's tables, to determine whether granting should occur.
The use of `compose-capability` here is somewhat artificial, but is used to
show a full definition covering all the possibilities:
```lisp
(defcap ALLOW_ENTRY (user-id:string)
  "Govern entry operation."
  (with-read table user-id
    { "guard" := guard, "active" := active }
    (enforce-guard guard)
    (enforce active "Only active users allowed entry"))
  (compose-capability (ANOTHER_CAPABILITY user-id)))
```

## `compose-capability`

The special form `compose-capability (CAP ARGS...)` can be used only within
the body of a `defcap`, and serves to extend the set of capabilities granted
by that capability, provided the predicates of the composed capabilities also
pass. Consider the following definition:
```lisp
(defcap FOO (user-id:string)
  (compose-capability (BAR user-id))
  (compose-capability (BAZ user-id)))
```

With this capability defined, the following two expressions become equivalent:
```lisp
(with-capability (FOO "bob")
  (call "alice"))

(with-capability (FOO "bob")
  (with-capability (BAR "bob")
    (with-capability (BAZ "bob")
      (call "alice"))))
```

The advantage to composing capabilities in the `defcap` form is that it always
grants the same set of three whenever `FOO` is granted.

## `with-capability`

## `require-capability`
