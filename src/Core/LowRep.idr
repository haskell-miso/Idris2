||| Two-level type theory, closure free code: the representation of types.
|||
||| 'Language.Staged.Low.LowRep t' is the run time representation of a type t
||| in low code (a 'LowTy'). It is solved here, during auto implicit search,
||| for every concrete type: primitive types, first order function types, and
||| data types (with a generated declaration, see 'declRef'). A type variable
||| needs a 'LowRep' in scope, as an ordinary auto implicit.
|||
||| This module also has the helpers for building the terms of the
||| representation of low code (lists, strings, ...), shared with
||| TTImp.LowQuote.
module Core.LowRep

import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.Value

import Data.List
import Libraries.Data.NatSet
import Libraries.Data.WithDefault

%default covering

||| A global name, as a term (with its name resolved)
export
globalRef : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core (Term vars)
globalRef fc n
    = do defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => throw (GenericMsg fc ("Low code needs " ++ show n))
         let nt = case definition def of
                       DCon t a _ => DataCon t a
                       TCon a _ _ _ _ _ _ => TyCon a
                       _ => Func
         pure (Ref fc nt (maybe n Resolved (getNameID n (gamma defs))))

||| A name in 'Language.Staged.Low'
export
lref : {auto c : Ref Ctxt Defs} -> FC -> String -> Core (Term vars)
lref fc s = globalRef fc (lowLibName s)

preludeName : String -> String -> Name
preludeName ns s = NS (mkNamespace ns) (UN (Basic s))

export
apps : FC -> Term vars -> List (Term vars) -> Term vars
apps fc f [] = f
apps fc f (a :: as) = apps fc (App fc f a) as

export
mkStr : FC -> String -> Term vars
mkStr fc s = PrimVal fc (Str s)

export
mkNat : {auto c : Ref Ctxt Defs} -> FC -> Nat -> Core (Term vars)
mkNat fc Z = globalRef fc (preludeName "Prelude.Types" "Z")
mkNat fc (S k) = pure (App fc !(globalRef fc (preludeName "Prelude.Types" "S")) !(mkNat fc k))

export
mkBool : {auto c : Ref Ctxt Defs} -> FC -> Bool -> Core (Term vars)
mkBool fc b = globalRef fc (preludeName "Prelude.Basics" (if b then "True" else "False"))

||| A list, with the type of its elements
export
mkList : {auto c : Ref Ctxt Defs} -> FC -> Term vars -> List (Term vars) -> Core (Term vars)
mkList fc ty [] = pure (App fc !(globalRef fc (preludeName "Prelude.Basics" "Nil")) ty)
mkList fc ty (x :: xs)
    = pure (apps fc !(globalRef fc (preludeName "Prelude.Basics" "::"))
                    [ty, x, !(mkList fc ty xs)])

export
mkJust : {auto c : Ref Ctxt Defs} -> FC -> Term vars -> Term vars -> Core (Term vars)
mkJust fc ty x = pure (apps fc !(globalRef fc (preludeName "Prelude.Types" "Just")) [ty, x])

export
mkNothing : {auto c : Ref Ctxt Defs} -> FC -> Term vars -> Core (Term vars)
mkNothing fc ty = pure (App fc !(globalRef fc (preludeName "Prelude.Types" "Nothing")) ty)

export
mkPair : {auto c : Ref Ctxt Defs} -> FC -> Term vars -> Term vars -> Term vars -> Term vars ->
         Core (Term vars)
mkPair fc a b x y = pure (apps fc !(globalRef fc (preludeName "Builtin" "MkPair")) [a, b, x, y])

||| A type in 'Language.Staged.Low' (with no arguments)
export
lowTypeRef : {auto c : Ref Ctxt Defs} -> FC -> String -> Core (Term vars)
lowTypeRef = lref

||| The constructor of 'LowTy' for a primitive type
primLowTy : {auto c : Ref Ctxt Defs} -> FC -> PrimType -> Core (Term vars)
primLowTy fc t
    = case t of
           IntType => lref fc "TInt"
           Int8Type => lref fc "TInt8"
           Int16Type => lref fc "TInt16"
           Int32Type => lref fc "TInt32"
           Int64Type => lref fc "TInt64"
           IntegerType => lref fc "TInteger"
           Bits8Type => lref fc "TBits8"
           Bits16Type => lref fc "TBits16"
           Bits32Type => lref fc "TBits32"
           Bits64Type => lref fc "TBits64"
           StringType => lref fc "TString"
           CharType => lref fc "TChar"
           DoubleType => lref fc "TDouble"
           WorldType => pure (App fc !(lref fc "TOther") (mkStr fc "%World"))

export
tOther : {auto c : Ref Ctxt Defs} -> FC -> String -> Core (Term vars)
tOther fc s = pure (App fc !(lref fc "TOther") (mkStr fc s))

export
tFun : {auto c : Ref Ctxt Defs} -> FC -> List (Term vars) -> Term vars -> Core (Term vars)
tFun fc as r = pure (apps fc !(lref fc "TFun") [!(mkList fc !(lowTypeRef fc "LowTy") as), r])

--------------------------------------------------------------------------
-- Declarations of data types

mutual
  ||| A reference to the 'LowDecl' of a data type: a generated definition in
  ||| the current namespace (shared by all uses in the module), which refers
  ||| to itself lazily when the type is recursive
  export
  declRef : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core (Term vars)
  declRef fc tn
      = do defs <- get Ctxt
           tfull <- toFullNames tn
           let dn = NS (currentNS defs) (UN (Basic ("lowDecl$" ++ show tfull)))
           dty <- lowTypeRef fc "LowDecl"
           case !(lookupCtxtExact dn (gamma defs)) of
                Just _ => pure (Ref fc Func dn)
                Nothing =>
                  do -- Reserve the name first, in case the type is recursive
                     ignore $ addDef dn (newDef fc dn top Scope.empty dty (specified Public) None)
                     body <- mkDecl fc tfull
                     ignore $ addDef dn
                         ({ flags := [Staged DMeta] }
                            (newDef fc dn top Scope.empty dty (specified Public)
                                    (PMDef defaultPI Scope.empty (STerm 0 body) (STerm 0 body) [])))
                     addToSave dn
                     log "elab.stage" 5 $ "Declaration of " ++ show tfull ++ " for low code"
                     pure (Ref fc Func dn)

  ||| The (lazy) declaration of a data type
  export
  lazyDecl : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core (Term vars)
  lazyDecl fc tn = pure (TDelay fc LLazy !(lowTypeRef fc "LowDecl") !(declRef fc tn))

  mkDecl : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core ClosedTerm
  mkDecl fc tn
      = do defs <- get Ctxt
           Just gdef <- lookupCtxtExact tn (gamma defs)
                | Nothing => throw (GenericMsg fc ("Unknown type " ++ show tn))
           let TCon arity _ _ _ _ mcons _ = definition gdef
                | _ => throw (GenericMsg fc (show tn ++ " is not a data type"))
           let cons = fromMaybe [] mcons
           cds <- traverse (conDecl arity) cons
           nts <- traverse isNewtypeCon cons
           pure (apps fc !(lref fc "MkLowDecl")
                    [ mkStr fc (show tn), !(mkNat fc arity),
                      !(mkBool fc (or (map delay nts) && length cons == 1)),
                      !(mkList fc !(lowTypeRef fc "LowConDecl") cds) ])
    where
      isNewtypeCon : Name -> Core Bool
      isNewtypeCon cn
          = do defs <- get Ctxt
               Just cdef <- lookupCtxtExact cn (gamma defs)
                    | Nothing => pure False
               case definition cdef of
                    DCon _ _ (Just _) => pure True
                    _ => pure False

      -- The kinds of the arguments of a constructor type, innermost first:
      -- Just p for the p-th parameter of the type
      fields : {vars : _} -> Nat -> Nat -> NatSet -> List (Maybe Nat) ->
               Term vars -> Core (List ClosedTerm)
      fields arity pos erase kinds (Bind _ x (Pi _ rig _ ty) sc)
          = do let isParam = pos < arity
               rest <- fields arity (S pos) erase
                              ((if isParam then Just pos else Nothing) :: kinds) sc
               if isParam || elem pos erase || isErased rig
                  then pure rest
                  else pure (!(synTy kinds ty) :: rest)
      fields _ _ _ _ _ = pure []

      conDecl : Nat -> Name -> Core ClosedTerm
      conDecl arity cn
          = do defs <- get Ctxt
               Just cdef <- lookupCtxtExact cn (gamma defs)
                    | Nothing => throw (GenericMsg fc ("Unknown constructor " ++ show cn))
               let DCon tag _ _ = definition cdef
                    | _ => throw (GenericMsg fc (show cn ++ " is not a constructor"))
               fs <- fields arity 0 (eraseArgs cdef) [] (type cdef)
               pure (apps fc !(lref fc "MkLowConDecl")
                        [ mkStr fc (show cn), PrimVal fc (I tag),
                          !(mkList fc !(lowTypeRef fc "LowTy") fs) ])

  synArgs : {auto c : Ref Ctxt Defs} -> {vars : _} ->
            List (Maybe Nat) -> Term vars -> Core (List ClosedTerm, ClosedTerm)
  synArgs kinds (Bind _ x (Pi _ _ _ dom) sc)
      = do d <- synTy kinds dom
           (ds, r) <- synArgs (Nothing :: kinds) sc
           pure (d :: ds, r)
  synArgs kinds ty = pure ([], !(synTy kinds ty))

  ||| The 'LowTy' of a type in a constructor declaration (syntactically: the
  ||| type parameters are TParam)
  synTy : {auto c : Ref Ctxt Defs} -> {vars : _} ->
          List (Maybe Nat) -> Term vars -> Core ClosedTerm
  synTy kinds ty
      = do let fc = getLoc ty
           case getFnArgs ty of
                (PrimVal _ (PrT t), []) => primLowTy fc t
                (Local _ _ idx _, []) =>
                    case getAt idx kinds of
                         Just (Just p) => pure (App fc !(lref fc "TParam") !(mkNat fc p))
                         _ => tOther fc "type variable"
                (Ref _ (TyCon _) n, args) =>
                    do args' <- traverse (synTy kinds) args
                       nfull <- toFullNames n
                       pure (apps fc !(lref fc "TData")
                                [ mkStr fc (show nfull),
                                  !(mkList fc !(lowTypeRef fc "LowTy") args'),
                                  !(lazyDecl fc nfull) ])
                (Bind _ x (Pi _ _ _ dom) sc, []) =>
                    do d <- synTy kinds dom
                       (ds, r) <- synArgs (Nothing :: kinds) sc
                       tFun fc (d :: ds) r
                _ => tOther fc "type"

--------------------------------------------------------------------------
-- The representation of a type

||| The 'LowTy' of a type in normal form. Type variables (and other types
||| that are not concrete) are looked up by searching for a 'LowRep'.
export
lowTyNF : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          FC -> Name -> Env Term vars -> NF vars -> Core (Term vars)
lowTyNF fc def env (NPrimVal _ (PrT t)) = primLowTy fc t
lowTyNF fc def env nf@(NBind _ x (Pi {}) _)
    = -- a function type: all its arguments, and the result
      do (ds, r) <- args nf
         tFun fc ds r
  where
    args : NF vars -> Core (List (Term vars), Term vars)
    args (NBind _ x (Pi _ rig _ dom) sc)
        = do defs <- get Ctxt
             d <- lowTyNF fc def env !(evalClosure defs dom)
             (ds, r) <- args !(sc defs (toClosure defaultOpts env (Erased fc Placeholder)))
             pure (d :: ds, r)
    args nf = pure ([], !(lowTyNF fc def env nf))
lowTyNF fc def env (NTCon _ n _ args)
    = do defs <- get Ctxt
         nfull <- toFullNames n
         if isCodeTyName nfull
            then tOther fc (show nfull)
            else do args' <- traverse (\a => lowTyNF fc def env !(evalClosure defs (snd a))) args
                    pure (apps fc !(lref fc "TData")
                             [ mkStr fc (show nfull),
                               !(mkList fc !(lowTypeRef fc "LowTy") args'),
                               !(lazyDecl fc nfull) ])
lowTyNF fc def env nf
    = -- not concrete: search for a LowRep (a type variable)
      do defs <- get Ctxt
         ty <- quote defs env nf
         rep <- globalRef fc (lowLibName "LowRep")
         dict <- search fc top False 20 def (App fc rep ty) env
         pure (apps fc !(lref fc "lowTyOfRep") [ty, dict])

||| Is this the full name of 'LowRep'?
export
isLowRep : {auto c : Ref Ctxt Defs} -> Name -> Core Bool
isLowRep n = pure (!(toFullNames n) == lowLibName "LowRep")

||| Built in search for 'LowRep t': for a concrete type t, its representation
export
lowRepBuiltin : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                FC -> Name -> Env Term vars -> NF vars -> Core (Maybe (Term vars))
lowRepBuiltin fc def env (NTCon _ n _ [(_, arg)])
    = if not !(isLowRep n) then pure Nothing else
      do defs <- get Ctxt
         anf <- evalClosure defs arg
         if concrete anf
            then do lty <- lowTyNF fc def env anf
                    ty <- quote defs env anf
                    pure (Just (apps fc !(lref fc "MkLowRep") [ty, lty]))
            else pure Nothing
  where
    concrete : NF vars -> Bool
    concrete (NPrimVal _ (PrT _)) = True
    concrete (NTCon {}) = True
    concrete (NBind _ _ (Pi {}) _) = True
    concrete _ = False
lowRepBuiltin fc def env _ = pure Nothing
