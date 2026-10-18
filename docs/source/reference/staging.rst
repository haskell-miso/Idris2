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

To use staging, import ``Language.Staged`` from ``base`` (and
``Language.Staged.Low`` for closure-free code, see below).

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

Closure-free code: ``Low``
==========================

``Language.Staged.Low`` adds the closure-free object language of the ICFP 2024
paper. ``Low a`` is a second kind of code, next to ``Code a``: the same
quotations and splices build it, and a quotation is ``Low`` code when its
type is ``Low a`` (otherwise it is ``Code``). Low code is a first order,
strict, monomorphic subset of Idris:

* values have *value types*: the primitive types, and data types whose
  fields are value types (no functions in data, no ``Code``);
* functions are first order. Their arguments are values, so no closures are
  ever needed at run time;
* ``let`` and function arguments are evaluated first (call by value);
* global functions used in low code are inlined. A recursive one becomes a
  local recursive function, specialised to the arguments that are known at
  compile time (such as a function argument of ``map``). Constructors,
  primitives, foreign functions and local definitions are used as they are.

.. code-block:: idris

    import Language.Staged.Low

    power : Nat -> Low Int -> Low Int
    power Z x = [|| 1 ||]
    power (S k) x = [|| ~x * ~(power k x) ||]

    cube : Int -> Int
    cube x = ~(power 3 [|| x ||])     -- low code runs as ordinary code

    -- a loop: a recursive low function
    sumSq : Low Int -> Low Int
    sumSq n = runGen $ do
      go <- genRecNamed "go" $ \go => [|| \i, acc => if i > ~n then acc else ~go (i + 1) (acc + i * i) ||]
      pure [|| ~go 1 0 ||]

Only low code can be spliced into low code. The implicit syntax works for
``Low`` as for ``Code``: ``sumSquares = sumSq`` and
``\n => runGen $ do go <- genRecNamed "go" $ \go => \i, acc => ...`` need no
annotations.

A generator which is polymorphic in a type used in low code needs a
``LowRep a`` constraint, which the compiler solves for every concrete type:

.. code-block:: idris

    twice : LowRep a => Low (a -> a) -> Low a -> Low a
    twice f x = genLetNamed "y" x $ \y => [|| ~f (~f ~y) ||]

``Gen`` (with ``gen``, ``genRec`` and ``named``) inserts lets and local
recursive functions, so the paper's examples carry over: pull streams whose
pipelines compile to a single loop, and monads by binding time improvement.
See ``tests/idris2/staging/staging011``.

Reflection and code generators
------------------------------

Low code can also be *reflected*: ``reflect : Low a -> LowProg`` gives a
first order syntax tree, with the type of every binder, after call saturation
(lambda lifting style: every call has all its arguments) and simplification.
It is a starting point for code generators written in Idris.
``lowPretty`` shows a program, and ``Language.Staged.Low.C.toC`` is an example
generator to C:

.. code-block:: idris

    import Language.Staged.Low.C

    sumSqLow : Low (Int -> Int)
    sumSqLow = [|| \n => ~(sumSq [|| n ||]) ||]

    main : IO ()
    main = putStr ~(lowString (toC "sumsq" (reflect sumSqLow)))

The C program is computed at compile time and spliced in as a string:

.. code-block:: c

    static int64_t go(int64_t n, int64_t i, int64_t acc) {
      int64_t r_0;
      switch ((i > n)) {
      case 0: {
      r_0 = go(n, (i + 1), (acc + (i * i))); break; }
      default: {
      r_0 = acc; break; }
      }
      return r_0;
    }

    int64_t sumsq(int64_t n) {
      return go(n, 1, 0);
    }

Errors in low code point at the term that is not low code:

.. code-block:: none

    higher : Low ((Int -> Int) -> Int)
    higher = [|| \g => g 1 ||]

    Error: low code: the lambda bound variable g must have a value type
    (first order data), not Int -> Int

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
* ``Code`` is ordinary Idris. ``Low`` code is closure free, but there is no
  support for join points beyond the inlining of local functions which are
  called once.
* The type of a recursive generator (``genRec``) can need an annotation when
  it is only determined by a later use, as unification in Idris can't always
  find it from the order in which the code is checked.
* A meta level argument of a specialised local function must be a variable,
  not a pattern.
