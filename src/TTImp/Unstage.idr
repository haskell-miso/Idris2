||| Two-level type theory: unstaging.
|||
||| Unstaging turns object level code containing splices into ordinary code,
||| by running the meta level programs in the splices and inserting the
||| object code they produce. This follows the "staging by evaluation"
||| algorithm of Kovács, "Staged Compilation with Two-Level Type Theory"
||| (ICFP 2022), section 4:
|||
||| * Meta level code is run by the ordinary evaluator. It is closed with
|||   respect to meta level variables, and object level variables only occur
|||   in it inside quotations, as neutral values.
||| * Object level code is not evaluated: it is copied, with the variables
|||   it captures read back from their values. In particular, unstaging
|||   performs no beta reduction, let inlining or unfolding of object level
|||   code ("strictness"), so the output is exactly the code the meta
|||   programs built.
||| * Object level binders are represented by fresh names, so the code
|||   produced under a binder never captures variables.
|||
||| Idris has no local case expressions or local functions in its core
||| language: they are lifted to global definitions which take the
||| variables in scope as arguments. When such a definition is object code
||| which captures meta level variables (a quotation containing a 'case', or
||| a local function, whose body uses a meta level variable in a splice),
||| it is "mixed", and unstaging specialises it to the values of the meta
||| level arguments at each call. Object level variables that those values
||| mention become extra arguments of the specialised definition.
module TTImp.Unstage

import Core.Case.CaseBuilder
import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Hash
import Core.LinearCheck
import Core.Normalise
import Core.Normalise.Quote
import Core.TT
import Core.UnifyState
import Core.Value

import Libraries.Data.NameMap
import Libraries.Data.WithDefault

import TTImp.Elab.Utils

import Data.List
import Libraries.Data.List.SizeOf
import Libraries.Data.NatSet

%default covering

-- Meta level code is run with everything visible (it only runs at compile
-- time)
stageOpts : EvalOpts
stageOpts = withAll

qopts : QuoteOpts
qopts = MkQuoteOpts True False Nothing

--------------------------------------------------------------------------
-- Variable manipulation

-- The variables (as indices into the scope) a term refers to
freeIdxs : Nat -> Term vs -> List Nat
freeIdxs d (Local _ _ idx _) = if idx >= d then [minus idx d] else []
freeIdxs d (Meta _ _ _ args) = concatMap (freeIdxs d) args
freeIdxs d (Bind _ _ b sc)
    = concatMap (freeIdxs d) (binderTerms b) ++ freeIdxs (S d) sc
  where
    binderTerms : Binder (Term vs') -> List (Term vs')
    binderTerms (Let _ _ v t) = [v, t]
    binderTerms (PLet _ _ v t) = [v, t]
    binderTerms b = [binderType b]
freeIdxs d (App _ f a) = freeIdxs d f ++ freeIdxs d a
freeIdxs d (As _ _ a p) = freeIdxs d a ++ freeIdxs d p
freeIdxs d (TDelayed _ _ t) = freeIdxs d t
freeIdxs d (TDelay _ _ t a) = freeIdxs d t ++ freeIdxs d a
freeIdxs d (TForce _ _ t) = freeIdxs d t
freeIdxs d (TQuote _ t a) = freeIdxs d t ++ freeIdxs d a
freeIdxs d (TSplice _ t) = freeIdxs d t
freeIdxs d (Erased _ (Dotted t)) = freeIdxs d t
freeIdxs d _ = []

indexVar : (vs : Scope) -> Nat -> Maybe (Var vs)
indexVar [] _ = Nothing
indexVar (x :: xs) Z = Just (MkVar First)
indexVar (x :: xs) (S k)
    = do MkVar p <- indexVar xs k
         pure (MkVar (Later p))

-- Replace the variables of the scope (outside depth 'd') by references to
-- the given names, making a term in another scope.
-- (De Bruijn indices of the inner variables don't change.)
toRefs : (Nat -> Maybe Name) -> Nat -> Term vs -> Maybe (Term vs')
toRefs f d (Local fc r idx p)
    = if idx < d
         then Just (Local {name = MN "toRefs" 0} fc r idx (believe_me p))
         else do n <- f (minus idx d)
                 pure (Ref fc Bound n)
toRefs f d (Ref fc nt n) = Just (Ref fc nt n)
toRefs f d (Meta fc n i args) = Meta fc n i <$> traverse (toRefs f d) args
toRefs f d (Bind fc x b sc)
    = Bind fc x <$> traverse (toRefs f d) b <*> toRefs f (S d) sc
toRefs f d (App fc fn a) = App fc <$> toRefs f d fn <*> toRefs f d a
toRefs f d (As fc s a p) = As fc s <$> toRefs f d a <*> toRefs f d p
toRefs f d (TDelayed fc r t) = TDelayed fc r <$> toRefs f d t
toRefs f d (TDelay fc r t a) = TDelay fc r <$> toRefs f d t <*> toRefs f d a
toRefs f d (TForce fc r t) = TForce fc r <$> toRefs f d t
toRefs f d (TQuote fc t a) = TQuote fc <$> toRefs f d t <*> toRefs f d a
toRefs f d (TSplice fc t) = TSplice fc <$> toRefs f d t
toRefs f d (PrimVal fc c) = Just (PrimVal fc c)
toRefs f d (Erased fc Impossible) = Just (Erased fc Impossible)
toRefs f d (Erased fc Placeholder) = Just (Erased fc Placeholder)
toRefs f d (Erased fc (Dotted t)) = Erased fc . Dotted <$> toRefs f d t
toRefs f d (TType fc u) = Just (TType fc u)

-- A closed term, with references to the given names turned into variables
closedIn : {fvs : _} -> Bounds fvs -> ClosedTerm -> Term fvs
closedIn bs tm = rewrite sym (appendNilRightNeutral fvs) in refsToLocals bs tm

-- Mark all variables as possibly let bound (the evaluator only looks up the
-- values of variables which might be let bound)
mayBeLet : Term vs -> Term vs
mayBeLet (Local fc _ idx p) = Local fc Nothing idx p
mayBeLet (Meta fc n i args) = Meta fc n i (map mayBeLet args)
mayBeLet (Bind fc x b sc) = Bind fc x (map mayBeLet b) (mayBeLet sc)
mayBeLet (App fc f a) = App fc (mayBeLet f) (mayBeLet a)
mayBeLet (As fc s a p) = As fc s (mayBeLet a) (mayBeLet p)
mayBeLet (TDelayed fc r t) = TDelayed fc r (mayBeLet t)
mayBeLet (TDelay fc r t a) = TDelay fc r (mayBeLet t) (mayBeLet a)
mayBeLet (TForce fc r t) = TForce fc r (mayBeLet t)
mayBeLet (TQuote fc t a) = TQuote fc (mayBeLet t) (mayBeLet a)
mayBeLet (TSplice fc t) = TSplice fc (mayBeLet t)
mayBeLet (Erased fc (Dotted t)) = Erased fc (Dotted (mayBeLet t))
mayBeLet tm = tm

metaPositions : Nat -> List Stage -> List Nat
metaPositions i [] = []
metaPositions i (SMeta :: ss) = i :: metaPositions (S i) ss
metaPositions i (_ :: ss) = metaPositions (S i) ss

getFnArgsFC : Term vs -> List (FC, Term vs) -> (Term vs, List (FC, Term vs))
getFnArgsFC (App fc f a) acc = getFnArgsFC f ((fc, a) :: acc)
getFnArgsFC f acc = (f, acc)

-- The free variable names of specialised definitions, by position
fvName : Nat -> Name
fvName i = MN "sfv" (cast i)

--------------------------------------------------------------------------
-- Building the variables of a specialised definition

-- An environment of the extra (object level) arguments of a specialised
-- definition, with the names they have in closed terms
mkFvEnv : FC -> List (Name, ClosedTerm) ->
          (fvs ** (Env Term fvs, Bounds fvs))
mkFvEnv fc tys = go (reverse tys)
  where
    go : List (Name, ClosedTerm) -> (fvs ** (Env Term fvs, Bounds fvs))
    go [] = (_ ** (Env.empty, None))
    go ((n, ty) :: rest)
        = let (fvs ** (env, bs)) = go rest in
              (_ ** (PVar fc top Explicit (closedIn bs ty) :: env,
                     Add n n bs))

-- The variables of an environment, as local variables, outermost first
envLocals : FC -> Env Term vs -> List (Term vs)
envLocals fc env = map (\ (MkVar p) => Local fc Nothing _ p) (reverse (allVars env))

-- Set the multiplicity of the given argument positions of a function type
-- to 0
eraseArgsTy : List Nat -> Nat -> Term vs -> Term vs
eraseArgsTy ms i (Bind fc x (Pi pfc c p ty) sc)
    = let c' = if i `elem` ms then erased else c in
          Bind fc x (Pi pfc c' p ty) (eraseArgsTy ms (S i) sc)
eraseArgsTy ms i tm = tm

-- Number of arguments in a function type
arity : Term vs -> Nat
arity (Bind _ _ (Pi {}) sc) = S (arity sc)
arity _ = Z

--------------------------------------------------------------------------
-- Staging

mutual
  ||| Stage object level code 'tm'. Its variables are 'cvars', bound to
  ||| values in 'locs' (object variables we've gone under, or meta level
  ||| values captured by a quotation), and 'free', the variables of the
  ||| definition being staged. 'bound' are the object binders we've gone
  ||| under while staging, and 'benv' is the environment of the output.
  stageTm : {auto c : Ref Ctxt Defs} ->
            {auto q : Ref QVar Int} ->
            {bound, free, cvars : _} ->
            Bounds bound -> Env Term (bound ++ free) ->
            Env Term free -> LocalEnv free cvars ->
            Term (cvars ++ free) -> Core (Term (bound ++ free))
  stageTm bounds benv env locs (Local fc r idx prf)
      = stageLocal bounds env fc r idx prf locs
  stageTm bounds benv env locs (Ref fc nt n) = pure (Ref fc nt n)
  stageTm bounds benv env locs (Meta fc n i args)
      = pure (Meta fc n i !(traverse (stageTm bounds benv env locs) args))
  stageTm bounds benv env locs (Bind fc x b sc)
      = do b' <- traverse (stageTm bounds benv env locs) b
           xn <- genName (nameRoot x)
           let var = MkNFClosure stageOpts env (NApp fc (NRef Bound xn) [])
           sc' <- stageTm (Add x xn bounds) (b' :: benv) env (var :: locs) sc
           pure (Bind fc x b' sc')
  stageTm bounds benv env locs tm@(App fc f a)
      = do let (fn, args) = getFnArgsFC tm []
           defs <- get Ctxt
           Just (n, gdef, stages) <- mixedHead defs fn
                | Nothing => pure (App fc !(stageTm bounds benv env locs f)
                                         !(stageTm bounds benv env locs a))
           specialiseCall bounds benv env locs fc n gdef stages args
  stageTm bounds benv env locs (As fc s a p)
      = pure (As fc s !(stageTm bounds benv env locs a)
                      !(stageTm bounds benv env locs p))
  stageTm bounds benv env locs (TDelayed fc r t)
      = pure (TDelayed fc r !(stageTm bounds benv env locs t))
  stageTm bounds benv env locs (TDelay fc r t a)
      = pure (TDelay fc r !(stageTm bounds benv env locs t)
                          !(stageTm bounds benv env locs a))
  stageTm bounds benv env locs (TForce fc r t)
      = pure (TForce fc r !(stageTm bounds benv env locs t))
  stageTm bounds benv env locs (TQuote fc _ _)
      = throw (GenericMsg fc "Staging: a quotation in object level code")
  stageTm bounds benv env locs (TSplice fc e)
      = do defs <- get Ctxt
           nf <- evalClosure defs (MkClosure stageOpts locs env e)
           case nf of
                NQuote _ _ body => stageClosure bounds benv env body
                _ => do tm <- quoteGenNF q qopts defs bounds env nf
                        throw (GenericMsg fc
                                 ("Staging: the splice did not compute to object code, but got stuck at " ++
                                  show !(toFullNames tm)))
  stageTm bounds benv env locs (PrimVal fc c) = pure (PrimVal fc c)
  stageTm bounds benv env locs (Erased fc Impossible) = pure (Erased fc Impossible)
  stageTm bounds benv env locs (Erased fc Placeholder) = pure (Erased fc Placeholder)
  stageTm bounds benv env locs (Erased fc (Dotted t))
      = pure (Erased fc (Dotted !(stageTm bounds benv env locs t)))
  stageTm bounds benv env locs (TType fc u) = pure (TType fc u)

  stageLocal : {auto c : Ref Ctxt Defs} ->
               {auto q : Ref QVar Int} ->
               {bound, free, cvars : _} ->
               Bounds bound -> Env Term free ->
               FC -> Maybe Bool ->
               (idx : Nat) -> (0 p : IsVar nm idx (cvars ++ free)) ->
               LocalEnv free cvars ->
               Core (Term (bound ++ free))
  -- One of the definition's own variables
  stageLocal bounds env fc r idx p []
      = case getBinder p env of
             -- a meta level variable of a specialised definition: its value
             Let _ _ val _ =>
                do defs <- get Ctxt
                   nf <- nf defs env val
                   quoteGenNF q qopts defs bounds env nf
             _ => let MkVar p' = weakenNs (mkSizeOf bound) (MkVar p) in
                      pure (Local fc r _ p')
  -- A variable bound to a value: read back the value. It's either an object
  -- variable, or a meta level value (of a primitive type, by stage checking)
  stageLocal bounds env fc r Z First (cl :: locs)
      = do defs <- get Ctxt
           nf <- evalClosure defs cl
           quoteGenNF q qopts defs bounds env nf
  stageLocal bounds env fc r (S idx) (Later p) (_ :: locs)
      = stageLocal bounds env fc r idx p locs

  ||| Stage the body of a quotation
  stageClosure : {auto c : Ref Ctxt Defs} ->
                 {auto q : Ref QVar Int} ->
                 {bound, free : _} ->
                 Bounds bound -> Env Term (bound ++ free) -> Env Term free ->
                 Closure free -> Core (Term (bound ++ free))
  stageClosure bounds benv _ (MkClosure _ locs env tm)
      = stageTm bounds benv env locs tm
  stageClosure bounds benv _ (MkNFClosure _ env nf)
      = do defs <- get Ctxt
           quoteGenNF q qopts defs bounds env nf

  ||| Is the head of an application a mixed definition (object code which
  ||| captures meta level variables)?
  mixedHead : {auto c : Ref Ctxt Defs} ->
              Defs -> Term vs -> Core (Maybe (Name, GlobalDef, List Stage))
  mixedHead defs (Ref _ Func n)
      = do Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => pure Nothing
           case defStage gdef of
                Just (DMixed stages) => pure (Just (n, gdef, stages))
                _ => pure Nothing
  mixedHead defs _ = pure Nothing

  ||| Specialise a call to a mixed definition to the values of its meta
  ||| level arguments
  specialiseCall : {auto c : Ref Ctxt Defs} ->
                   {auto q : Ref QVar Int} ->
                   {bound, free, cvars : _} ->
                   Bounds bound -> Env Term (bound ++ free) ->
                   Env Term free -> LocalEnv free cvars ->
                   FC -> Name -> GlobalDef -> List Stage ->
                   List (FC, Term (cvars ++ free)) ->
                   Core (Term (bound ++ free))
  specialiseCall bounds benv env locs fc n gdef stages args
      = do defs <- get Ctxt
           fn <- toFullNames n
           let ar = arity (type gdef)
           when (length args < ar) $
              throw (GenericMsg fc ("Staging: the local definition " ++ show fn ++
                                    " uses meta level variables, so must be applied to all its arguments in object code"))
           let metaPos = metaPositions 0 stages
           -- The values of the meta level arguments
           let indexed = zip [0 .. length args] args
           vals <- traverse (\ (i, (afc, a)) =>
                               do nf <- evalClosure defs (MkClosure stageOpts locs env a)
                                  tm <- quoteGenNF q qopts defs bounds env nf
                                  pure (i, tm))
                            (filter (\ (i, _) => i `elem` metaPos) indexed)
           -- The object level variables they mention, closed under the
           -- variables their types mention, outermost first
           fvIdxs <- fvClosure benv (nub (concatMap (freeIdxs 0 . snd) vals))
           let fvs = sortBy (\x, y => compare y x) fvIdxs
           let fvMap = zip fvs (map fvName [0 .. length fvs])
           let lookupFv = \i => lookup i fvMap
           let Just closedVals
                   = traverse (\ (i, v) => map (i,) (the (Maybe ClosedTerm) (toRefs lookupFv 0 v))) vals
               | Nothing => throw (InternalError "Staging: can't close specialised arguments")
           fvTys <- traverse (\i => do Just (MkVar p) <- pure (indexVar (bound ++ free) i)
                                           | Nothing => throw (InternalError "Staging: bad variable")
                                       tynf <- nf defs benv (binderType (getBinder p benv))
                                       ty <- quote defs benv tynf
                                       let Just cty = the (Maybe ClosedTerm) (toRefs lookupFv 0 ty)
                                           | Nothing => throw (InternalError "Staging: can't close variable type")
                                       pure (fvName' fvMap i, cty))
                             fvs
           -- The name of the specialisation, determined by the values
           let h = hashWithSalt (hash (show fn)) (map snd closedVals)
           sn <- inCurrentNS (MN ("staged " ++ show fn) h)
           Nothing <- lookupCtxtExact sn (gamma defs)
               | Just _ => mkCall sn fvs metaPos
           log "compile.stage" 5 $ "Specialising " ++ show fn ++ " to " ++ show sn
           mkSpecialised fc sn gdef metaPos closedVals fvTys
           mkCall sn fvs metaPos
    where
      fvName' : List (Nat, Name) -> Nat -> Name
      fvName' m i = fromMaybe (fvName i) (lookup i m)

      mkCall : Name -> List Nat -> List Nat -> Core (Term (bound ++ free))
      mkCall sn fvs metaPos
          = do fvArgs <- traverse (\i => do Just (MkVar p) <- pure (indexVar (bound ++ free) i)
                                               | Nothing => throw (InternalError "Staging: bad variable")
                                            pure (Local fc Nothing _ p)) fvs
               args' <- traverse (\ (i, (afc, a)) =>
                                     if i `elem` metaPos
                                        then pure (afc, Erased afc Placeholder)
                                        else do a' <- stageTm bounds benv env locs a
                                                pure (afc, a'))
                                 (zip [0 .. length args] args)
               pure (applyStackWithFC (apply fc (Ref fc Func sn) fvArgs) args')

  -- Add the variables mentioned by the types of the given variables
  fvClosure : {auto c : Ref Ctxt Defs} ->
              {vs : _} ->
              Env Term vs -> List Nat -> Core (List Nat)
  fvClosure benv is
      = do defs <- get Ctxt
           more <- traverse (\i => do Just (MkVar p) <- pure (indexVar vs i)
                                         | Nothing => pure []
                                      tynf <- nf defs benv (binderType (getBinder p benv))
                                      ty <- quote defs benv tynf
                                      pure (freeIdxs 0 ty)) is
           let new = filter (\i => not (i `elem` is)) (nub (concat more))
           if isNil new
              then pure is
              else fvClosure benv (is ++ new)

  ||| Make the specialisation 'sn' of the mixed definition 'gdef', with the
  ||| given values for the meta level arguments, and extra (leading)
  ||| arguments for the object level variables the values mention
  mkSpecialised : {auto c : Ref Ctxt Defs} ->
                  {auto q : Ref QVar Int} ->
                  FC -> Name -> GlobalDef ->
                  (metaPos : List Nat) ->
                  (vals : List (Nat, ClosedTerm)) ->
                  (fvTys : List (Name, ClosedTerm)) ->
                  Core ()
  mkSpecialised fc sn gdef metaPos vals fvTys
      = do let PMDef _ _ _ _ pats = definition gdef
                 | _ => throw (GenericMsg fc ("Staging: can't specialise " ++ show !(toFullNames gdef.fullname)))
           let (fvs ** (fvEnv, fvBounds)) = mkFvEnv fc fvTys
           -- The meta level arguments become erased (they are not used any
           -- more once staged)
           let fty = abstractEnvType fc fvEnv (embed (eraseArgsTy metaPos 0 (type gdef)))
           -- Add the definition first, so that recursive calls find it
           ignore $ addDef sn (newDef fc sn top Scope.empty fty (specified Public) None)
           clauses <- traverse (specClause fvs fvEnv fvBounds) pats
           (cargs ** (tree_ct, _)) <- getPMDef fc (CompileTime top) sn fty clauses
           rclauses <- traverse eraseClause clauses
           (rargs ** (tree_rt, _)) <- getPMDef fc RunTime sn fty rclauses
           let Just Refl = scopeEq cargs rargs
               | Nothing => throw (InternalError "Staging: inconsistent case trees")
           (erasedArgs, dterased) <- findErased fty
           defs <- get Ctxt
           Just sdef <- lookupCtxtExact sn (gamma defs)
                | Nothing => throw (InternalError "Staging: lost definition")
           ignore $ addDef sn ({ definition := PMDef defaultPI rargs tree_ct tree_rt
                                                     (map toPats clauses),
                                 eraseArgs := erasedArgs,
                                 safeErase := dterased } sdef)
           addToSave sn
           logC "compile.stage" 5 $
               do t <- toFullNames tree_rt
                  pure ("Specialised " ++ show sn ++ ":\n" ++ show t)
    where
      toPats : Clause -> (vs ** (Env Term vs, Term vs, Term vs))
      toPats (MkClause env lhs rhs) = (_ ** (env, lhs, rhs))

      eraseClause : Clause -> Core Clause
      eraseClause (MkClause env lhs rhs)
          = do u <- newRef UST initUState
               lhs' <- linearCheck fc linear True env lhs
               rhs' <- linearCheck fc linear True env rhs
               pure (MkClause env lhs' rhs')

      -- The value of the meta level argument bound by this pattern
      metaArgVar : List (Term vs) -> List (Nat, Nat) -- argument pos, variable index
      metaArgVar args
          = mapMaybe (\ (i, a) => if i `elem` metaPos
                                     then map (i,) (patVar a)
                                     else Nothing)
                     (zip [0 .. length args] args)
        where
          patVar : Term vs -> Maybe Nat
          patVar (Local _ _ idx _) = Just idx
          patVar (As _ _ _ (Local _ _ idx _)) = Just idx
          patVar (As _ _ (Local _ _ idx _) _) = Just idx
          patVar _ = Nothing

      -- Rebuild the clause's environment over the extra variables, with the
      -- meta level variables bound to their values
      extendEnv : {vs, fvs : _} -> Bounds fvs -> List (Nat, ClosedTerm) ->
                  Nat -> Env Term vs -> Env Term fvs -> Env Term (vs ++ fvs)
      extendEnv fb mvals i [] fenv = fenv
      extendEnv {vs = v :: vs'} fb mvals i (b :: env) fenv
          = let rest = extendEnv fb mvals (S i) env fenv in
                case lookup i mvals of
                     Just val =>
                        let val' = weakenNs (mkSizeOf vs') (closedIn fb val) in
                            Let (binderLoc b) (multiplicity b) val'
                                (embed (binderType b)) :: rest
                     Nothing => map embed b :: rest

      -- Turn the let bound meta level variables back into (erased) pattern
      -- variables
      unLet : Env Term vs -> Env Term vs
      unLet [] = []
      unLet (Let lfc _ _ ty :: env) = PVar lfc erased Explicit ty :: unLet env
      unLet (b :: env) = b :: unLet env

      specClause : (fvs : Scope) -> Env Term fvs -> Bounds fvs ->
                   (vs ** (Env Term vs, Term vs, Term vs)) -> Core Clause
      specClause fvs fvEnv fvBounds (vs ** (env, lhs, rhs))
          = do let (_, largs) = getFnArgs lhs
               let mvars = metaArgVar largs
               when (length mvars /= length metaPos) $
                  throw (GenericMsg fc ("Staging: can't specialise " ++ show !(toFullNames gdef.fullname) ++
                                        " (a meta level argument is matched by a pattern)"))
               let mvals = mapMaybe (\ (i, idx) => map (idx,) (lookup i vals)) mvars
               let env' = extendEnv fvBounds mvals 0 env fvEnv
               -- stage the right hand side with the meta level variables
               -- bound to their values
               rhs' <- stageTm {cvars = Scope.empty} None env' env' []
                               (embed (mayBeLet rhs))
               let fvArgs = map (weakenNs (mkSizeOf vs)) (envLocals fc fvEnv)
               let lhs' = apply fc (Ref fc Func sn) (fvArgs ++ map embed largs)
               pure (MkClause (unLet env') lhs' rhs')

||| Does a term contain a splice?
export
hasSplice : Term vars -> Bool
hasSplice (TSplice _ _) = True
hasSplice (Meta _ _ _ args) = any hasSplice args
hasSplice (Bind _ _ b sc)
    = hasSplice (binderType b) || hasSplice sc ||
      case b of
           Let _ _ v _ => hasSplice v
           _ => False
hasSplice (App _ f a) = hasSplice f || hasSplice a
hasSplice (As _ _ a p) = hasSplice a || hasSplice p
hasSplice (TDelayed _ _ t) = hasSplice t
hasSplice (TDelay _ _ t a) = hasSplice t || hasSplice a
hasSplice (TForce _ _ t) = hasSplice t
hasSplice (TQuote _ t a) = hasSplice t || hasSplice a
hasSplice (Erased _ (Dotted t)) = hasSplice t
hasSplice _ = False

-- Does a term call a mixed definition (which needs specialising)?
callsMixed : {auto c : Ref Ctxt Defs} -> Term vars -> Core Bool
callsMixed tm
    = do defs <- get Ctxt
         anyM (isMixed defs) (keys (getRefs (UN Underscore) tm))
  where
    isMixed : Defs -> Name -> Core Bool
    isMixed defs n
        = do Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             case defStage gdef of
                  Just (DMixed _) => pure True
                  _ => pure False

||| Unstage an object level term, in the environment of the definition
||| it belongs to: run all the splices, and insert the code they produce.
export
unstage : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Env Term vars -> Term vars -> Core (Term vars)
unstage env tm
    = if not (hasSplice tm) && not !(callsMixed tm)
         then pure tm
         else do q <- newRef QVar 0
                 res <- stageTm {cvars = Scope.empty} None env env [] tm
                 logTerm "compile.stage" 5 "Staged" res
                 pure res
