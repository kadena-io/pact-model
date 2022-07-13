# Capabilities

## What is a capability?

In the general sense, a **capability** is a means of granting the capability
to perform some action from one part of a system to another.

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

### `defcap`

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
    (enforce active "Only active users allowed entry")
    (compose-capability (ANOTHER_CAPABILITY user-id))))
```

### `compose-capability`

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

### `with-capability`

The special form `with-capability (CAP ARGS...) EXPR` does five things:

1. It checks to see if `CAP ARGS...` has already been granted. If so, evaluate
   `EXPR` and return.

2. It calls the predicate for `CAP`, passing it `ARGS...`, and creates the
   capability token if it passes (along with any others that were composed
   with that capability).

3. It pushes this set of granted tokens onto the call stack, so that future
   calls to `require-capability` can check for them.

4. It evaluates `EXPR`.

5. Revoke any tokens granted by popping them from the call stack. This scopes
   the lifetime of the granted capabilities to the evaluation of this call to
   `with-capability`.

In summary, `with-capability` is used to ensure that a given capability (or
capabilities, if composed) can be granted at a certain point, and sets up the
evaluator so that calls to `require-capability` can confirm this fact later
on.

### `require-capability`

The special form `require-capability (CAP ARGS...)` simply tests whether the
given capability `CAP ARGS...` had been granted earlier by `with-capability`;
if not, it raises an error.

### Managed capabilities

Pact also provides a service called "managed capabilities", although this is a
bit of a misnomer. What it is really is a managed resource associated with a
capability as described above. Although the syntax blends the two concepts for
convenience, they are still separate and will be documented here as such.

In brief, a managed capability is a capability that can only be granted if a
diminishing amount of a certain resource still remains. Think of a watering
can: I can only use it to water my plants if there is water still in the can;
and each time I use it, that much water disappears. Once it is empty, no more
watering can occur.

We will look again at each of the capability operations, since their meaning
changes slightly in the presence of this managed resource.

### `defcap`

To define a managed capability, three additional things are required:

1. An argument associated with the resource. Note that this argument also
   contributes to the identity of the granted token, as show in the example
   below.

2. An `@managed` section that both names this argument and gives the name of a
   "management function" for decrementing the resource.

3. A definition of that "management function". This function always receives
   two arguments of the same type as the resource: the current amount, and the
   amount requested in the call to `with-capability`.

Here is a classic example used by coin contracts to limit how much may be
transferred during a particular transaction:
```lisp
(defcap TRANSFER (sender:string receiver:string amount:decimal)
  @managed amount TRANSFER_mgr
  (ensure (> amount 0) "Amount must be non-zero"))

(defun TRANSFER_mgr:decimal (managed:decimal requested:decimal)
  (enforce (>= managed requested) "Transfer quantity exhausted")
  (- managed requested) ;; update managed quantity for next time
)
```

In this definition, the name of the capability is `TRANSFER`; the arguments
associated with its capability tokens are `sender`, `receiver` and `amount`;
and the argument associated with the resource is also `amount`.

Aside from the managed resource, managed capabilities are identical to
unmanaged capabilities: They are granted by passing the capability name and
arguments to `with-capability`, and they are checked by passing that same name
and arguments to `require-capability`. The differences all relate to that new
managed argument, and when the management function is called.

### `install-capability`

NOTE: This function really ought to be called `install-resource`, because it
does not grant nor install a capability token in the way that
`with-capability` does. It installs an initial resource amount in a special
internal table that is associated with the specified capability.

So the special form `install-capability (CAP ARGS...)` does two things:

1. It looks up which of the `ARGS...` is the managed argument.

2. It installs that value into a special resource table in the current the
   evaluation environment, keyed by `CAP ARGS...` *but without that argument*.

To understand that second point a little better, let's look at the transfer
example again. It was defined as:
```lisp
(defcap TRANSFER (sender:string receiver:string amount:decimal)
  @managed amount TRANSFER_mgr
  ...)
```

When we call `(install-capability (TRANSFER "bob" "alice" 100))`, behind the
scenes it is calling a hypothetical `install-resource-internal` function like this:
```lisp
(install-resource-internal (TRANSFER "bob" "alice") 100)
```

In this way, any future invocations of `with-capability` that mention `"bob"`
and `"alice"` (in that order) will each deduct from this same resource until
there is no more left.

### `with-capability`

The special `with-capability (CAP ARGS...)` in the case of managed
capabilities is very similar to unmanaged capabilities, as described above,
except for a new set of steps after step 3 in the section on unmanaged
`with-capability` above, after the predicate has successfully passed:

1. Lookup the current value of the resource named by `CAP ARGS...`, but where
   `ARGS` does not contain the resource value. In our running transfer
   example, this would be just `(TRANSFER "bob" "alice")`.

2. Take the value given in `ARGS...` that is associated with the resource.

3. Pass the current amount from 3a and the requested amount from 3b both to
   the management function associated with the capability.

4. If it passes, use the amount returned by the management function to update
   the remaining amount available in the internal resource table. Note that
   resource consumption is not scoped: it persists beyond the call to
   `with-capability`.

Other than these additional steps related to managing the resource, all the
others details of `with-capability` remain the same. The granted token is
identified by `CAP ARGS...`, including the requested resource amount, and all
these details must be mentioned exactly by `require-capability` as before.

Here is a brief example that puts all of this together, assuming the same
`TRANSFER` capability defined above:
```lisp
(install-capability (TRANSFER "bob" "alice" 100))
;; the available amount of resource is now 100

(with-capability (TRANSFER "bob" "alice" 20)
  ;; the remaining amount of resource is now 80
  (require-capability (TRANSFER "bob" "alice" 20)))

;; the remaining amount of resource is still 80
```

To repeat what was mentioned above: the first argument to `require-capability`
must always exactly match an earlier call to `with-capability`, no matter the
type of capability.
