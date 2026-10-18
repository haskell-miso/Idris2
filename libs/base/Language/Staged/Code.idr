||| Two-level type theory: the type of object level code. (Re-exported by
||| Language.Staged, and used by Language.Staged.Low.)
module Language.Staged.Code

%default total

||| The type of object level code of type 'a'. Values of 'Code a' only exist
||| at compile time; they are built with quotations, and used by splices.
public export
data Code : Type -> Type where
