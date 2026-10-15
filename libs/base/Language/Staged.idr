||| Two-level type theory: staged compilation.
|||
||| Code has two stages: the *meta level*, which runs at compile time, and the
||| *object level*, which runs at run time.
|||
|||   Code a      -- the meta level type of object level code of type a
|||   [|| e ||]   -- quotation:  if e : a (object level), [|| e ||] : Code a
|||   ~e          -- splice:     if e : Code a (meta level), ~e : a
|||
||| with ~[|| e ||] = e and [|| ~e ||] = e. A definition whose type mentions
||| 'Code' only exists at compile time; a definition containing a splice is
||| object code, whose splices are run by the compiler ("staging") before it
||| is compiled. Everything else (including the Prelude) can be used at both
||| stages.
|||
||| For example, the power function, with the exponent known at compile time:
|||
|||   power : Nat -> Code Int -> Code Int
|||   power Z x = [|| 1 ||]
|||   power (S k) x = [|| ~x * ~(power k x) ||]
|||
|||   cube : Int -> Int
|||   cube x = ~(power 3 [|| x ||])     -- compiles to x * (x * (x * 1))
|||
||| Most quotations and splices can be left out: the elaborator inserts them
||| where the types make it unambiguous, e.g. 'power (S k) x = x * power k x'
||| and 'cube x = power 3 x'.
|||
||| See: András Kovács, "Staged Compilation with Two-Level Type Theory",
||| ICFP 2022, and "Closure-Free Functional Programming in a Two-Level Type
||| Theory", ICFP 2024.
module Language.Staged

import Data.List

%default total

||| The type of object level code of type 'a'. Values of 'Code a' only exist
||| at compile time; they are built with quotations, and used by splices.
public export
data Code : Type -> Type where

--------------------------------------------------------------------------
-- Lifting meta level values to object level code ("serialisation")

||| Turn a meta level value into object level code which computes it. For
||| primitive types, the value becomes a literal.
public export
interface Lift a where
  lift : a -> Code a

public export
Lift Int where
  lift x = [|| x ||]

public export
Lift Integer where
  lift x = [|| x ||]

public export
Lift Double where
  lift x = [|| x ||]

public export
Lift Char where
  lift x = [|| x ||]

public export
Lift String where
  lift x = [|| x ||]

public export
Lift Bits8 where
  lift x = [|| x ||]

public export
Lift Bits16 where
  lift x = [|| x ||]

public export
Lift Bits32 where
  lift x = [|| x ||]

public export
Lift Bits64 where
  lift x = [|| x ||]

public export
Lift Nat where
  lift Z = [|| Z ||]
  lift (S k) = [|| S ~(lift k) ||]

public export
Lift Bool where
  lift True = [|| True ||]
  lift False = [|| False ||]

public export
Lift () where
  lift () = [|| () ||]

public export
Lift a => Lift (Maybe a) where
  lift Nothing = [|| Nothing ||]
  lift (Just x) = [|| Just ~(lift x) ||]

public export
Lift a => Lift (List a) where
  lift [] = [|| [] ||]
  lift (x :: xs) = [|| ~(lift x) :: ~(lift xs) ||]

public export
(Lift a, Lift b) => Lift (a, b) where
  lift (x, y) = [|| (~(lift x), ~(lift y)) ||]

public export
(Lift a, Lift b) => Lift (Either a b) where
  lift (Left x) = [|| Left ~(lift x) ||]
  lift (Right y) = [|| Right ~(lift y) ||]

||| The code of a list, from the code of its elements
public export
liftList : List (Code a) -> Code (List a)
liftList [] = [|| [] ||]
liftList (x :: xs) = [|| ~x :: ~(liftList xs) ||]

--------------------------------------------------------------------------
-- Binding time improvement: moving between code of functions and functions
-- on code

||| A meta level function on code, from the code of a function. Applying it
||| makes an object level application.
public export
up : Code (a -> b) -> Code a -> Code b
up f x = [|| ~f ~x ||]

||| The code of a function, from a meta level function on code. The function
||| is inlined into the body of the object level lambda.
public export
down : (Code a -> Code b) -> Code (a -> b)
down f = [|| \x => ~(f [|| x ||]) ||]

--------------------------------------------------------------------------
-- The code generation monad: let insertion

||| Code generators in continuation passing style, so that they can insert
||| object level let bindings around the code they generate. (Kovács,
||| "Closure-Free Functional Programming in a Two-Level Type Theory".)
public export
record Gen (a : Type) where
  constructor MkGen
  unGen : {0 r : Type} -> (a -> Code r) -> Code r

public export
Functor Gen where
  map f (MkGen g) = MkGen (\k => g (k . f))

public export
Applicative Gen where
  pure x = MkGen (\k => k x)
  MkGen f <*> MkGen x = MkGen (\k => f (\f' => x (\x' => k (f' x'))))

public export
Monad Gen where
  MkGen x >>= f = MkGen (\k => x (\x' => unGen (f x') k))

||| Run a code generator
public export
runGen : Gen (Code a) -> Code a
runGen (MkGen g) = g id

||| Bind the given code to an object level variable, and continue with the
||| code of the variable. This avoids duplicating the code (and the work it
||| does at run time) when the result is used more than once.
public export
gen : Code a -> Gen (Code a)
gen x = MkGen (\k => [|| let v = ~x in ~(k [|| v ||]) ||])
