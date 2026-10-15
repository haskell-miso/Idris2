.. _ref-sect-staging:

************************************
Staged compilation (two-level types)
************************************

Idris supports *staged compilation* based on two-level type theory (2LTT),
following András Kovács, `Staged Compilation with Two-Level Type Theory
<https://andraskovacs.github.io/pdfs/2ltt.pdf>`_ (ICFP 2022) and
`Closure-Free Functional Programming in a Two-Level Type Theory
<https://andraskovacs.github.io/pdfs/2ltt_icfp24.pdf>`_ (ICFP 2024).

Every term belongs to one of two *stages*:

* the **meta level**, which runs at compile time, and
* the **object level**, which is compiled and runs at run time.

Meta level programs compute object level code. Compiling a program runs its
meta level parts and leaves only object level code. The output is guaranteed
to contain no trace of the meta level: abstractions such as higher order
functions, interpreters or type classes used at the meta level cost nothing
at run time.

To use staging, import ``Language.Staged`` from ``base``.

Code, quotations and splices
============================

There are three term formers:

.. code-block:: idris

    Code a      -- the meta level type of object level code of type a
    [|| e ||]   -- quotation: if e : a is object level, [|| e ||] : Code a
    ~e          -- splice:    if e : Code a is meta level, ~e : a

They satisfy ``~[|| e ||] = e`` and ``[|| ~e ||] = e``. For example, here is
``power``, with the exponent known at compile time:

.. code-block:: idris

    import Language.Staged

    power : Nat -> Code Int -> Code Int
    power Z x = [|| 1 ||]
    power (S k) x = [|| ~x * ~(power k x) ||]

    cube : Int -> Int
    cube x = ~(power 3 [|| x ||])

``cube`` compiles to ``\x => x * (x * (x * 1))``. The recursion on ``Nat``
happens entirely at compile time.

Which definitions are at which stage
------------------------------------

Stages are inferred, so they are never written down:

* A definition whose type mentions ``Code`` is **meta level**. It exists only
  at compile time and is never passed to a code generator.
* A definition containing a splice is **object level**. Its splices are run
  ("staged") before it is compiled.
* A definition whose stage the body does not fix (most of the Prelude, for
  example) can be used at **both** stages.

Variables bound at one stage can only be used at that stage. For instance,
an object level variable can't be inspected by meta level code:

.. code-block:: none

    bad : Int -> Int
    bad x = ~(if x == 0 then [|| 1 ||] else [|| 2 ||])

    Error: The variable x is at the object level (run time), but it is used
    at the meta level (compile time).

The one exception is *cross-stage persistence* for primitive types: a meta
level ``Int``, ``String``, ``Double`` and so on can be used in object code,
and becomes a literal. The ``Lift`` interface extends this to other data:
``lift : Lift a => a -> Code a``.

Types are erased and not staged, so they can mention meta level computation
freely, for example ``Vec 3 Int`` below.

Implicit syntax
===============

Most quotations and splices can be omitted. When the type of an expression
and its expected type are at different stages, the elaborator inserts the
coercion, as in Kovács's stage inference. The following program has no
staging annotations at all, and stages exactly like the explicit version:

.. code-block:: idris

    power : Nat -> Code Int -> Code Int
    power Z x = 1
    power (S k) x = x * power k x

    cube : Int -> Int
    cube x = power 3 x

    mapC : (Code a -> Code b) -> Code (List a) -> Code (List b)
    mapC f xs = foldr (\y, ys => f y :: ys) [] xs

    incAll : List Int -> List Int
    incAll xs = mapC (\v => v + 1) xs           -- a single foldr

    -- object level types computed at compile time
    Vec : Nat -> Code Type -> Code Type
    Vec Z a = ()
    Vec (S k) a = (a, Vec k a)

    total3 : Vec 3 Int -> Int
    total3 (x, y, z, ()) = x + y + z

The rules are:

* An object level expression (a literal, lambda, constructor or object level
  function application) used where ``Code a`` is expected is **quoted**.
* A meta level expression of type ``Code a`` used where an ``a`` is expected
  is **spliced**. Partially applied code, as in ``f y :: ys`` above, is
  spliced at the head.
* A ``case`` on a meta level value inside object code is run at compile
  time, so the whole ``case`` is spliced.

When the stage is ambiguous, write the quotation or splice explicitly. Both
forms can be mixed freely.

Object code capturing meta level values
=======================================

A ``case`` block or a local function inside a quotation can refer to meta
level variables. Here, ``f`` is a meta level function inlined into the body
of an object level recursive function:

.. code-block:: idris

    mapC : (Code a -> Code b) -> Code (List a) -> Code (List b)
    mapC f xs = [|| let go : List a -> List b
                        go [] = []
                        go (y :: ys) = ~(f [|| y ||]) :: go ys
                     in go ~xs ||]

    addAll : Int -> List Int -> List Int
    addAll n xs = ~(mapC (\v => [|| ~v + n ||]) [|| xs ||])

Each call site gets its own specialised copy of ``go``. The meta level
arguments are substituted and staged, and the object level variables it
captures (``n`` here) become extra arguments.

The ``Gen`` monad
=================

Splicing the same code twice duplicates its run time work.
``Language.Staged`` provides the code generation monad of the ICFP 2024
paper, which can insert object level ``let`` bindings:

.. code-block:: idris

    gen : Code a -> Gen (Code a)        -- let-bind the code, return the variable
    runGen : Gen (Code a) -> Code a

It also provides binding time improvement between ``Code (a -> b)`` and
``Code a -> Code b`` (``up`` and ``down``).

Inspecting the output
=====================

To see the staged code for each object level definition, use:

.. code-block:: idris

    %logging "compile.stage" 5

Further examples are in ``tests/idris2/staging``. They include a staged
interpreter for the simply typed lambda calculus and foldr/build fusion.

Limitations
===========

* There is no stage polymorphism beyond definitions that are usable at both
  stages. A function can't be generic over whether its argument is code.
* Object level code is ordinary Idris. There is no closure-free target
  language or join point support yet.
* A meta level argument of a specialised local function must be a variable,
  not a pattern.
