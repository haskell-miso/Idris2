||| Two-level type theory, closure free code: splicing low code into object
||| code.
|||
||| A splice ~e in object level code whose value is low code ('MkLow', the
||| representation built by the code generated in TTImp.LowQuote) is read
||| back as ordinary code (MicroHs's lowToExp): the higher order binders are
||| applied to fresh variables, a case becomes a case expression, and a
||| recursive let a local function. The result is elaborated where the splice
||| is, so the code that it becomes is compiled as usual. Idris is strict, so
||| the strict semantics of low code (lets, arguments and fields are
||| evaluated) is the ordinary one.
module TTImp.LowUnstage

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.LowRep
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab
import TTImp.Elab.Check
import TTImp.TTImp

import Data.List
import Data.List1
import Data.String
import Libraries.Data.List.SizeOf
import Libraries.Data.WithDefault

%default covering

||| The name of a constructor of the representation of low code
conName : {auto c : Ref Ctxt Defs} -> Name -> Core (Maybe String)
conName n
    = do n' <- toFullNames n
         case n' of
              NS ns (UN (Basic s)) =>
                  pure (if ns == lowNS then Just s else Nothing)
              _ => pure Nothing

||| A name, from the string 'reflect' and the code generators see (the full
||| name, shown)
parseName : String -> Name
parseName s
    = let (ns, n) = go [] (unpack s) in
          if null ns then UN (Basic (unparen n))
                     else NS (mkNamespace (joinBy "." (reverse ns))) (UN (Basic (unparen n)))
  where
    -- the namespace: identifiers starting with a capital letter, each
    -- followed by '.'; the rest is the name
    go : List String -> List Char -> (List String, String)
    go acc cs
        = case span (\c => isAlphaNum c || c == '_' || c == '\'') cs of
               (seg@(c :: _), '.' :: rest@(_ :: _)) =>
                   if isUpper c then go (pack seg :: acc) rest else (acc, pack cs)
               _ => (acc, pack cs)

    -- an operator is shown in parentheses
    unparen : String -> String
    unparen n = case unpack n of
                     ('(' :: rest@(_ :: _)) =>
                         case reverse rest of
                              (')' :: op) => pack (reverse op)
                              _ => n
                     _ => n

data LowVarNo : Type where

record RB (vs : Scope) where
  constructor MkRB
  rbFC : FC
  rbEnv : Env Term vs
  ||| The object level variables bound by the staging, by their names in
  ||| the evaluated code
  rbBound : List (Name, Name)
  ||| The next variable number
  rbNext : Ref LowVarNo Int


lowFail : FC -> String -> Core a
lowFail fc msg = throw (GenericMsg fc ("Staging low code: " ++ msg))


mutual
  ||| An object level term (the value of HObj, or a meta level value) as
  ||| surface syntax
  termRaw : {vs : _} -> {auto c : Ref Ctxt Defs} ->
            RB vs -> Term vs -> Core RawImp
  termRaw rb (Local fc _ idx p) = pure (IVar fc (nameAt p))
  termRaw rb (Ref fc Bound n)
      = case lookup n (rbBound rb) of
             Just x => pure (IVar fc x)
             Nothing => pure (IVar fc n)
  termRaw rb (Ref fc _ n) = pure (IVar fc !(toFullNames n))
  termRaw rb (App fc f a) = pure (IApp fc !(termRaw rb f) !(termRaw rb a))
  termRaw rb (PrimVal fc c) = pure (IPrimVal fc c)
  termRaw rb (Erased fc _) = pure (Implicit fc False)
  termRaw rb tm = lowFail (rbFC rb) ("cannot read back " ++ show !(toFullNames tm))

  ||| A type of low code as surface syntax
  tyRaw : {vs : _} -> {auto c : Ref Ctxt Defs} ->
          RB vs -> NF vs -> Core RawImp
  tyRaw rb nf
      = do let fc = rbFC rb
           defs <- get Ctxt
           case nf of
                NDCon _ n _ _ args =>
                    do Just con <- conName n
                            | Nothing => pure (Implicit fc False)
                       args' <- traverse (\a => evalClosure defs (snd a)) args
                       case (con, args') of
                            ("TInt", _) => prim IntType
                            ("TInteger", _) => prim IntegerType
                            ("TInt8", _) => prim Int8Type
                            ("TInt16", _) => prim Int16Type
                            ("TInt32", _) => prim Int32Type
                            ("TInt64", _) => prim Int64Type
                            ("TBits8", _) => prim Bits8Type
                            ("TBits16", _) => prim Bits16Type
                            ("TBits32", _) => prim Bits32Type
                            ("TBits64", _) => prim Bits64Type
                            ("TDouble", _) => prim DoubleType
                            ("TChar", _) => prim CharType
                            ("TString", _) => prim StringType
                            ("TFun", [as, r]) =>
                                do as' <- listNF as
                                   as'' <- traverse (tyRaw rb) as'
                                   r' <- tyRaw rb r
                                   pure (foldr (\a, b => IPi fc top Explicit Nothing a b) r' as'')
                            ("TData", [n, as, _]) =>
                                do NPrimVal _ (Str nm) <- pure n
                                        | _ => pure (Implicit fc False)
                                   as' <- traverse (tyRaw rb) !(listNF as)
                                   pure (foldl (IApp fc) (IVar fc (parseName nm)) as')
                            _ => pure (Implicit fc False)
                _ => pure (Implicit fc False)
    where
      prim : PrimType -> Core RawImp
      prim t = pure (IPrimVal (rbFC rb) (PrT t))

  ||| The elements of a list (in normal form)
  listNF : {vs : _} -> {auto c : Ref Ctxt Defs} -> NF vs -> Core (List (NF vs))
  listNF (NDCon _ n _ _ args)
      = do defs <- get Ctxt
           case (nameRoot !(toFullNames n), reverse args) of
                ("::", (_, t) :: (_, h) :: _) =>
                    do h' <- evalClosure defs h
                       t' <- evalClosure defs t
                       pure (h' :: !(listNF t'))
                _ => pure []
  listNF _ = pure []

  ||| A literal as surface syntax
  litRaw : {vs : _} -> {auto c : Ref Ctxt Defs} -> RB vs -> NF vs -> Core RawImp
  litRaw rb (NDCon _ n _ _ args)
      = do let fc = rbFC rb
           defs <- get Ctxt
           args' <- traverse (\a => evalClosure defs (snd a)) args
           case (!(conName n), args') of
                (Just "LitFixed", [t, NPrimVal _ (BI i)]) =>
                    do NDCon _ tn _ _ _ <- pure t
                            | _ => lowFail fc "a literal of an unknown type"
                       Just tc <- conName tn
                            | Nothing => lowFail fc "a literal of an unknown type"
                       pure (IPrimVal fc (fixed tc i))
                (Just _, [NPrimVal _ c]) => pure (IPrimVal fc c)
                _ => lowFail fc "a literal that is not known at compile time"
    where
      fixed : String -> Integer -> Constant
      fixed "TInt8" i = I8 (cast i)
      fixed "TInt16" i = I16 (cast i)
      fixed "TInt32" i = I32 (cast i)
      fixed "TInt64" i = I64 (cast i)
      fixed "TBits8" i = B8 (cast i)
      fixed "TBits16" i = B16 (cast i)
      fixed "TBits32" i = B32 (cast i)
      fixed _ i = B64 (cast i)
  litRaw rb _ = lowFail (rbFC rb) "a literal of an unknown type"

  ||| A fresh object level variable, for a binder of low code: its name, and
  ||| the representation of the variable to apply the binder to
  freshVar : {vs : _} -> {auto c : Ref Ctxt Defs} ->
             RB vs -> String -> Core (Name, Term vs)
  freshVar rb x
      = do let fc = rbFC rb
           i <- get LowVarNo @{rbNext rb}
           put LowVarNo @{rbNext rb} (i + 1)
           let n = UN (Basic (x ++ "_l" ++ show i))
           hv <- lref fc "HVar"
           pure (n, apps fc hv [PrimVal fc (I i), mkStr fc (show n),
                                App fc !(lref fc "TOther") (mkStr fc "variable")])

  ||| Apply a binder of low code (a meta level function) to arguments
  applyNF : {vs : _} -> {auto c : Ref Ctxt Defs} ->
            RB vs -> Closure vs -> List (Term vs) -> Core (NF vs)
  applyNF rb f args
      = do defs <- get Ctxt
           go defs !(evalClosure defs f) args
    where
      go : Defs -> NF vs -> List (Term vs) -> Core (NF vs)
      go defs nf [] = pure nf
      go defs (NBind _ _ (Lam {}) sc) (a :: as)
          = go defs !(sc defs (toClosure withAll (rbEnv rb) a)) as
      go defs fnf as
          = do ftm <- quote defs (rbEnv rb) fnf
               nfOpts withAll defs (rbEnv rb) (apps (rbFC rb) ftm as)

  ||| Read back low code as surface syntax
  lowRaw : {vs : _} -> {auto c : Ref Ctxt Defs} ->
           RB vs -> NF vs -> Core RawImp
  lowRaw rb nf
      = do let fc = rbFC rb
           defs <- get Ctxt
           case nf of
                NDCon _ n _ _ args =>
                    do Just con <- conName n
                            | Nothing => lowFail fc ("not low code: " ++ show !(toFullNames n))
                       lowCon rb con (map snd args)
                _ => do tm <- quote defs (rbEnv rb) nf
                        lowFail fc ("the low code did not compute, but got stuck at " ++
                                    show !(toFullNames tm))

  lowCon : {vs : _} -> {auto c : Ref Ctxt Defs} ->
           RB vs -> String -> List (Closure vs) -> Core RawImp
  lowCon rb con args
      = do let fc = rbFC rb
           defs <- get Ctxt
           case (con, args) of
                ("HVar", [_, n, _]) =>
                    do NPrimVal _ (Str x) <- evalClosure defs n
                            | _ => lowFail fc "a variable without a name"
                       pure (IVar fc (UN (Basic x)))
                ("HObj", [_, _, _, v]) =>
                    do vnf <- evalClosure defs v
                       termRaw rb !(quote defs (rbEnv rb) vnf)
                ("HLam", [x, t, f]) =>
                    do NPrimVal _ (Str xs) <- evalClosure defs x
                            | _ => lowFail fc "a lambda without a name"
                       (n, var) <- freshVar rb xs
                       ty <- tyRaw rb !(evalClosure defs t)
                       body <- lowRaw rb !(applyNF rb f [var])
                       pure (ILam fc top Explicit (Just n) ty body)
                ("HApp", [f, as]) =>
                    do f' <- lowRaw rb !(evalClosure defs f)
                       as' <- traverse (lowRaw rb) !(listNF !(evalClosure defs as))
                       pure (foldl (IApp fc) f' as')
                ("HLet", [x, mt, e, f]) =>
                    do NPrimVal _ (Str xs) <- evalClosure defs x
                            | _ => lowFail fc "a let without a name"
                       (n, var) <- freshVar rb xs
                       ty <- case !(evalClosure defs mt) of
                                  NDCon _ jn _ _ [_, (_, t)] => tyRaw rb !(evalClosure defs t)
                                  _ => pure (Implicit fc False)
                       e' <- lowRaw rb !(evalClosure defs e)
                       body <- lowRaw rb !(applyNF rb f [var])
                       pure (ILet fc fc top n ty e' body)
                ("HLetRec", [xts, f]) => lowLetRec rb xts f
                ("HCase", [s, cons, alts, d]) =>
                    do s' <- lowRaw rb !(evalClosure defs s)
                       altnfs <- listNF !(evalClosure defs alts)
                       alts' <- traverse (lowAlt rb) altnfs
                       ncons <- length <$> listNF !(evalClosure defs cons)
                       d' <- case !(evalClosure defs d) of
                                  NDCon _ jn _ _ [_, (_, de)] =>
                                      do de' <- lowRaw rb !(evalClosure defs de)
                                         pure [PatClause fc (Implicit fc True) de']
                                  _ => -- a case that doesn't cover all the
                                       -- constructors (e.g. after an
                                       -- impossible case): fail otherwise
                                       pure (if length altnfs < ncons
                                                then [PatClause fc (Implicit fc True)
                                                         (IApp fc (IVar fc (UN (Basic "idris_crash")))
                                                                  (IPrimVal fc (Str "no match")))]
                                                else [])
                       pure (ICase fc [] s' (Implicit fc False) (alts' ++ d'))
                ("HCaseLit", [s, alts, d]) =>
                    do s' <- lowRaw rb !(evalClosure defs s)
                       alts' <- traverse (litAlt rb) !(listNF !(evalClosure defs alts))
                       d' <- lowRaw rb !(evalClosure defs d)
                       pure (ICase fc [] s' (Implicit fc False)
                                   (alts' ++ [PatClause fc (Implicit fc True) d']))
                ("HCon", [con, _, as]) =>
                    do NDCon _ _ _ _ cargs <- evalClosure defs con
                            | _ => lowFail fc "a constructor without a name"
                       (_, cn) :: _ <- pure cargs
                            | _ => lowFail fc "a constructor without a name"
                       NPrimVal _ (Str cs) <- evalClosure defs cn
                            | _ => lowFail fc "a constructor without a name"
                       as' <- traverse (lowRaw rb) !(listNF !(evalClosure defs as))
                       pure (foldl (IApp fc) (IVar fc (parseName cs)) as')
                ("HLit", [l, _]) => litRaw rb !(evalClosure defs l)
                ("HPrim", [p, _]) =>
                    do NPrimVal _ (Str ps) <- evalClosure defs p
                            | _ => lowFail fc "a primitive without a name"
                       pure (IVar fc (parseName ps))
                ("HForeign", [h, _, _]) =>
                    do NPrimVal _ (Str hs) <- evalClosure defs h
                            | _ => lowFail fc "a foreign function without a name"
                       pure (IVar fc (parseName hs))
                ("HFail", [m]) =>
                    do NPrimVal _ (Str ms) <- evalClosure defs m
                            | _ => lowFail fc "an error without a message"
                       pure (IApp fc (IVar fc (UN (Basic "idris_crash"))) (IPrimVal fc (Str ms)))
                _ => lowFail fc ("not low code: " ++ con)

  lowAlt : {vs : _} -> {auto c : Ref Ctxt Defs} ->
           RB vs -> NF vs -> Core ImpClause
  lowAlt rb (NDCon _ _ _ _ [(_, con), (_, names), (_, f)])
      = do let fc = rbFC rb
           defs <- get Ctxt
           NDCon _ _ _ _ cargs <- evalClosure defs con
                | _ => lowFail fc "an alternative without a constructor"
           (_, cn) :: _ <- pure cargs
                | _ => lowFail fc "an alternative without a constructor"
           NPrimVal _ (Str cs) <- evalClosure defs cn
                | _ => lowFail fc "an alternative without a constructor"
           ns <- listNF !(evalClosure defs names)
           vars <- traverse (\n => do NPrimVal _ (Str x) <- pure n
                                           | _ => freshVar rb "x"
                                      freshVar rb x) ns
           lst <- mkList fc !(lref fc "LowExp") (map snd vars)
           body <- lowRaw rb !(applyNF rb f [lst])
           pure (PatClause fc (foldl (IApp fc) (IVar fc (parseName cs))
                                     (map (IBindVar fc . fst) vars))
                           body)
  lowAlt rb _ = lowFail (rbFC rb) "not an alternative"

  litAlt : {vs : _} -> {auto c : Ref Ctxt Defs} ->
           RB vs -> NF vs -> Core ImpClause
  litAlt rb (NDCon _ _ _ _ args)
      = do let fc = rbFC rb
           defs <- get Ctxt
           case reverse args of
                (_, e) :: (_, l) :: _ =>
                    do l' <- litRaw rb !(evalClosure defs l)
                       e' <- lowRaw rb !(evalClosure defs e)
                       pure (PatClause fc l' e')
                _ => lowFail fc "not an alternative"
  litAlt rb _ = lowFail (rbFC rb) "not an alternative"

  ||| A recursive let: local functions
  lowLetRec : {vs : _} -> {auto c : Ref Ctxt Defs} ->
              RB vs -> Closure vs -> Closure vs -> Core RawImp
  lowLetRec rb xts f
      = do let fc = rbFC rb
           defs <- get Ctxt
           bs <- listNF !(evalClosure defs xts)
           decls <- traverse (\b => do NDCon _ _ _ _ pargs <- pure b
                                            | _ => lowFail fc "a recursive let without names"
                                       case reverse pargs of
                                            (_, t) :: (_, x) :: _ =>
                                                do NPrimVal _ (Str xs) <- evalClosure defs x
                                                        | _ => lowFail fc "a recursive let without names"
                                                   (n, var) <- freshVar rb xs
                                                   pure (n, var, !(evalClosure defs t))
                                            _ => lowFail fc "a recursive let without names") bs
           lst <- mkList fc !(lref fc "LowExp") (map (\(_, v, _) => v) decls)
           NDCon _ _ _ _ pair <- applyNF rb f [lst]
                | _ => lowFail fc "a recursive let whose body is not a pair"
           (_, b) :: (_, rhss) :: _ <- pure (reverse pair)
                | _ => lowFail fc "a recursive let whose body is not a pair"
           rhss' <- traverse (lowRaw rb) !(listNF !(evalClosure defs rhss))
           body <- lowRaw rb !(evalClosure defs b)
           tys <- traverse (\(_, _, t) => tyRaw rb t) decls
           let claims = zipWith (\(n, _, _), ty =>
                                    IClaim (MkFCVal fc (MkIClaimData top Private
                                              -- (low code can be partial, like
                                              -- the primitives it uses)
                                              [Totality PartialOK]
                                              (Mk [fc, MkFCVal fc n] ty)))) decls tys
           let defs = zipWith (\(n, _, _), rhs => IDef fc n [PatClause fc (IVar fc n) rhs])
                              decls rhss'
           pure (ILocal fc (claims ++ defs) body)

boundList : Bounds bs -> List (Name, Name)
boundList None = []
boundList (Add x xn rest) = (xn, x) :: boundList rest

||| Read back the low code that a splice computed (a 'MkLow', evaluated in the
||| environment of the definition) as object code, under the object level
||| binders that staging has gone under
export
lowSplice : {free, bound : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            FC -> Name -> Env Term free -> Bounds bound -> Env Term (bound ++ free) ->
            NF free -> Core (Maybe (Term (bound ++ free)))
lowSplice fc def env bounds benv (NDCon _ n _ _ [(_, aty), (_, e)])
    = do n' <- toFullNames n
         if n' /= lowLibName "MkLow" then pure Nothing else
           do defs <- get Ctxt
              q <- newRef LowVarNo 0
              let rb = MkRB fc env (boundList bounds) q
              raw <- lowRaw rb !(evalClosure defs e)
              ty <- quote defs env !(evalClosure defs aty)
              log "compile.stage" 5 $ "Low code as object code: " ++ show raw
              let Just idx = getNameID def (gamma defs)
                   | Nothing => lowFail fc ("no definition " ++ show def)
              let ty' = weakenNs (mkSizeOf bound) ty
              tm <- checkTerm idx InExpr [] (MkNested []) benv raw (gnf benv ty')
              pure (Just tm)
lowSplice fc def env bounds benv _ = pure Nothing
