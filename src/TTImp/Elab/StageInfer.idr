||| Two-level type theory: inferring quotations and splices.
|||
||| Most quotations and splices can be left out of staged programs: the
||| elaborator inserts them where the types make the intended stage
||| unambiguous. This follows the coercive subtyping of Kovács' 2LTT
||| elaborator (A ≤ Code A inserts a quotation, Code A ≤ A a splice), in the
||| syntax directed style of the MicroHs implementation, deciding by the head
||| of an application:
|||
||| * At the meta level, an expression checked against 'Code a' which cannot
|||   itself have that type is quoted: a literal, a lambda, an object level
|||   variable, a meta level variable of a primitive type (whose value
|||   persists into the code as a literal), or an application whose head
|||   cannot return code (its result is another type constructor, or a type
|||   variable constrained by an interface, as in 'x * y'). Meta level code with a 'Code' result is
|||   left alone, so that the meta level reading is used when it is possible.
||| * At the object level, a meta level variable or application whose result
|||   is 'Code a' is spliced. A meta level variable of type 'Code (a -> b)'
|||   applied to arguments has its head spliced.
||| * A definition whose stage is not known yet becomes object level code
|||   when its body is a meta level application with a 'Code' result,
|||   checked against a type which is not 'Code' (e.g. 'cube x = power 3 x').
|||
||| For example:
|||
|||   power : Nat -> Code Int -> Code Int
|||   power Z x = 1                      -- [|| 1 ||]
|||   power (S k) x = x * power k x      -- [|| ~x * ~(power k x) ||]
|||
|||   cube : Int -> Int
|||   cube x = power 3 x                 -- ~(power 3 [|| x ||])
|||
||| A coercion is only inserted where checking the expression as written
||| would fail, so it never changes the meaning of a program which checks
||| without it. Explicit quotations and splices are always available to
||| choose another reading.
module TTImp.Elab.StageInfer

import Core.Env
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Stage
import TTImp.Elab.Staged
import TTImp.TTImp

import Libraries.Data.NameMap

%default covering

-- The head of an application, and the number of explicit arguments
getHead : RawImp -> Nat -> (RawImp, Nat)
getHead (IApp _ f _) n = getHead f (S n)
getHead (IAutoApp _ f _) n = getHead f n
getHead (INamedApp _ f _ _) n = getHead f n
getHead f n = (f, n)

-- Replace the head of an application
replaceHead : RawImp -> RawImp -> RawImp
replaceHead new (IApp fc f a) = IApp fc (replaceHead new f) a
replaceHead new (IAutoApp fc f a) = IAutoApp fc (replaceHead new f) a
replaceHead new (INamedApp fc f n a) = INamedApp fc (replaceHead new f) n a
replaceHead new f = new

-- What sort of type a function returns, after some explicit arguments
data ResultKind
   = RCode
   | RCodeOver Nat -- returns code after this many arguments, and has more
   | RFunCode Nat -- a function returning code after this many more arguments
   | RVar
   | RConcrete
   | RUnknown

-- What we know about the head of an application
record HeadInfo where
  constructor MkHeadInfo
  stage : Maybe Stage   -- Nothing: stage polymorphic, or unknown
  result : ResultKind   -- the result after the given arguments
  isCodeVal : Bool      -- the head itself has type 'Code a'
  constrained : Bool    -- has auto implicit (interface) arguments

-- Classify the result of a function type after 'n' explicit arguments
resultKind : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Env Term vars -> Nat -> NF vars -> Core (ResultKind, Bool)
resultKind env n ty = go n False ty
  where
    -- How many more explicit arguments until the result is 'Code'?
    codeAfter : Nat -> NF vars -> Core (Maybe Nat)
    codeAfter m (NBind fc x (Pi _ _ Explicit aty) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts env (Erased fc Placeholder))
             codeAfter (S m) sc'
    codeAfter m (NBind fc x (Pi _ _ _ aty) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts env (Erased fc Placeholder))
             codeAfter m sc'
    codeAfter m nf
        = if isJust !(isCodeNF nf) then pure (Just m) else pure Nothing

    go : Nat -> Bool -> NF vars -> Core (ResultKind, Bool)
    go k cons nf@(NBind fc x (Pi _ _ Explicit aty) sc)
        = case k of
               Z => do Just m <- codeAfter Z nf
                            | Nothing => pure (RConcrete, cons) -- a function is not code
                       pure (RFunCode m, cons)
               S k' => do defs <- get Ctxt
                          sc' <- sc defs (toClosure defaultOpts env (Erased fc Placeholder))
                          go k' cons sc'
    go k cons (NBind fc x (Pi _ _ AutoImplicit aty) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts env (Erased fc Placeholder))
             go k True sc'
    go k cons (NBind fc x (Pi _ _ _ aty) sc)
        = do defs <- get Ctxt
             sc' <- sc defs (toClosure defaultOpts env (Erased fc Placeholder))
             go k cons sc'
    go (S k) cons nf
        = do Just _ <- isCodeNF nf
                  | Nothing => pure (RUnknown, cons)
             -- code applied to more arguments
             pure (RCodeOver (minus n (S k)), cons)
    go Z cons nf
        = do Nothing <- isCodeNF nf
                  | Just _ => pure (RCode, cons)
             pure (classify nf, cons)
      where
        classify : NF vars -> ResultKind
        classify (NErased {}) = RVar -- an implicit argument we instantiated
        classify (NApp _ (NLocal {}) _) = RVar
        classify (NApp _ (NRef Bound _) _) = RVar
        classify (NApp _ (NMeta {}) _) = RUnknown
        classify (NApp _ (NRef _ _) _) = RUnknown -- stuck function
        classify (NTCon {}) = RConcrete
        classify (NPrimVal {}) = RConcrete
        classify (NType {}) = RConcrete
        classify (NBind {}) = RConcrete
        classify (NDelayed {}) = RConcrete
        classify _ = RUnknown

isCodeTy : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> NF vars -> Core Bool
isCodeTy nf = pure (isJust !(isCodeNF nf))

-- Information about the head of an application, if it's a name we know
headInfo : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           NestedNames vars -> Env Term vars ->
           RawImp -> Nat -> Core (Maybe HeadInfo)
headInfo nest env (IVar fc n) nargs
    = case lookup n (names nest) of
           Just (nestn, argns, _) =>
              do defs <- get Ctxt
                 let n' = fromMaybe n nestn
                 Just ndef <- lookupCtxtExact n' (gamma defs)
                      | Nothing => pure Nothing
                 -- the nested definition is applied to its environment first
                 tynf <- nf defs env (embed (type ndef))
                 global ndef (length argns + nargs) tynf
           Nothing =>
              case defined n env of
                   Just (MkIsDefined {idx} _ lv) =>
                      do defs <- get Ctxt
                         tynf <- nf defs env (binderType (getBinder lv env))
                         (res, cons) <- resultKind env nargs tynf
                         codeVal <- isCodeTy tynf
                         st <- getStageState
                         vstage <- if active st
                                      then localStage vars n idx
                                      else pure Nothing
                         -- If we don't know the variable's stage (e.g. in a
                         -- type), a variable of type 'Code a' is meta level
                         let vstage' = case vstage of
                                            Nothing => if codeVal then Just SMeta else Nothing
                                            Just s => Just s
                         pure (Just (MkHeadInfo vstage' res codeVal cons))
                   Nothing =>
                      do defs <- get Ctxt
                         [(_, _, gdef)] <- lookupCtxtName n (gamma defs)
                              | _ => pure Nothing -- ambiguous: can't tell
                         tynf <- nf defs env (embed (type gdef))
                         global gdef nargs tynf
  where
    global : GlobalDef -> Nat -> NF vars -> Core (Maybe HeadInfo)
    global gdef k tynf
        = do (res, cons) <- resultKind env k tynf
             let s = case defStage gdef of
                          Just DMeta => Just SMeta
                          Just DObj => Just SObj
                          Just (DMixed _) => Just SObj
                          Nothing => Nothing
             pure (Just (MkHeadInfo s res False cons))
headInfo nest env _ _ = pure Nothing

isOver : ResultKind -> Bool
isOver (RCodeOver _) = True
isOver _ = False

-- Is this a meta level expression whose value is code?
isCodeExpr : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             NestedNames vars -> Env Term vars -> RawImp -> Core Bool
isCodeExpr nest env tm
    = do let (hd, nargs) = getHead tm Z
         Just info <- headInfo nest env hd nargs
              | Nothing => pure False
         case info.result of
              RCode => pure True
              _ => pure (info.isCodeVal && nargs == 0)

-- Is this a meta level expression whose value is not code (e.g. a meta level
-- variable of type 'Nat')? A case on it, at the object level, is a compile
-- time choice between pieces of code.
isMetaNonCode : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                NestedNames vars -> Env Term vars -> RawImp -> Core Bool
isMetaNonCode nest env tm
    = do let (hd, nargs) = getHead tm Z
         Just info <- headInfo nest env hd nargs
              | Nothing => pure False
         case info.stage of
              Just SMeta =>
                 case info.result of
                      RConcrete => pure (not info.isCodeVal)
                      RVar => pure (not info.isCodeVal)
                      _ => pure False
              _ => pure False

-- Is this a meta level variable of a primitive type (e.g. 'n : Int')? It
-- can't be code, but quoting it persists its value into the code (as a
-- literal, see 'checkLocalStage')
metaPrimVar : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              NestedNames vars -> Env Term vars -> RawImp -> Core Bool
metaPrimVar nest env (IVar fc n)
    = do st <- getStageState
         let True = active st && isNothing (lookup n (names nest))
              | False => pure False
         let Just (MkIsDefined {idx} _ lv) = defined n env
              | Nothing => pure False
         Just SMeta <- localStage vars n idx
              | _ => pure False
         defs <- get Ctxt
         NPrimVal _ (PrT _) <- nf defs env (binderType (getBinder lv env))
              | _ => pure False
         pure True
metaPrimVar nest env _ = pure False

-- Can this expression, checked against 'Code a' at the meta level, not have
-- that type as it is? Then it's object code, and needs quoting.
mustQuote : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            NestedNames vars -> Env Term vars -> RawImp -> Core Bool
mustQuote nest env (IPrimVal _ _) = pure True
mustQuote nest env (ILam {}) = pure True
mustQuote nest env (IPi {}) = pure True
mustQuote nest env (IType {}) = pure True
-- a case (or if) on code is object level
mustQuote nest env (ICase _ _ scr _ _) = isCodeExpr nest env scr
mustQuote nest env (IAlternative _ _ (alt :: _)) = mustQuote nest env alt
mustQuote nest env tm
    = do let (hd, nargs) = getHead tm Z
         Just info <- headInfo nest env hd nargs
              | Nothing => case hd of
                                IPrimVal _ _ => pure True
                                _ => pure False
         case info.stage of
              Just SObj => pure True -- object code used at the meta level
              Just SMeta =>
                  -- code applied to arguments is an object application
                  if (info.isCodeVal && nargs > 0) || isOver info.result
                     then pure True
                     else pure (nargs == 0 && !(metaPrimVar nest env hd))
              Nothing =>
                  case info.result of
                       RCode => pure False
                       RCodeOver _ => pure True
                       RFunCode _ => pure False
                       RConcrete => pure True
                       RVar => pure info.constrained
                       RUnknown => pure False

-- Application spines
data AppArg = AExp FC RawImp | AAuto FC RawImp | ANamed FC Name RawImp

spine : RawImp -> List AppArg -> (RawImp, List AppArg)
spine (IApp fc f a) acc = spine f (AExp fc a :: acc)
spine (IAutoApp fc f a) acc = spine f (AAuto fc a :: acc)
spine (INamedApp fc f n a) acc = spine f (ANamed fc n a :: acc)
spine f acc = (f, acc)

rebuild : RawImp -> List AppArg -> RawImp
rebuild f [] = f
rebuild f (AExp fc a :: as) = rebuild (IApp fc f a) as
rebuild f (AAuto fc a :: as) = rebuild (IAutoApp fc f a) as
rebuild f (ANamed fc n a :: as) = rebuild (INamedApp fc f n a) as

-- Split the arguments after 'k' explicit arguments
splitExplicit : Nat -> List AppArg -> (List AppArg, List AppArg)
splitExplicit Z as = ([], as)
splitExplicit (S k) [] = ([], [])
splitExplicit (S k) (AExp fc a :: as)
    = let (xs, ys) = splitExplicit k as in (AExp fc a :: xs, ys)
splitExplicit (S k) (a :: as)
    = let (xs, ys) = splitExplicit (S k) as in (a :: xs, ys)

-- Is this a meta level expression with a 'Code' result, used at the object
-- level? Then it needs splicing: return the expression with the splice
-- inserted
needsSplice : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              NestedNames vars -> Env Term vars -> RawImp ->
              Maybe (Glued vars) ->
              Core (Maybe RawImp)
needsSplice nest env tm@(ICase fc _ scr _ _) exp
    = if !(isMetaNonCode nest env scr)
         then pure (Just (IUnquote fc tm))
         else pure Nothing
needsSplice nest env tm exp
    = do let (hd, nargs) = getHead tm Z
         Just info <- headInfo nest env hd nargs
              | Nothing => pure Nothing
         let fc = getFC tm
         case info.stage of
              Just SMeta =>
                 if info.isCodeVal && nargs > 0
                    then -- code applied to arguments: splice the head
                         pure (Just (replaceHead (IUnquote (getFC hd) hd) tm))
                    else case info.result of
                              RCode => pure (Just (IUnquote fc tm))
                              RCodeOver k =>
                                 -- code applied to more arguments: splice
                                 -- the code part
                                 do let (f, args) = spine tm []
                                    let (pre, post) = splitExplicit k args
                                    let pre' = rebuild f pre
                                    pure (Just (rebuild (IUnquote (getFC pre') pre') post))
                              RFunCode m =>
                                 -- a meta level function on code, where an
                                 -- object level function is expected:
                                 -- eta expand it
                                 do Just expty <- pure exp
                                         | Nothing => pure Nothing
                                    NBind {} <- getNF expty
                                         | _ => pure Nothing
                                    ns <- traverse (\_ => genVarName "eta") [1 .. m]
                                    let body = foldl (\f, n => IApp fc f (IVar fc n)) tm ns
                                    pure (Just (foldr (\n, sc => ILam fc top Explicit (Just n)
                                                                     (Implicit fc False) sc)
                                                      body ns))
                              _ => pure Nothing
              _ => pure Nothing

-- Is this a meta level variable of type 'Code a' (or 'Low a') applied to
-- arguments?
codeApplied : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              NestedNames vars -> Env Term vars -> RawImp -> Core Bool
codeApplied nest env tm
    = do let (hd, nargs) = getHead tm Z
         if nargs == 0 then pure False else
           do Just info <- headInfo nest env hd nargs
                   | Nothing => pure False
              pure (info.isCodeVal && info.stage == Just SMeta)

isExplicitStaging : RawImp -> Bool
isExplicitStaging (IStageQuote {}) = True
isExplicitStaging (IUnquote {}) = True
isExplicitStaging (IHole {}) = True
isExplicitStaging (Implicit {}) = True
isExplicitStaging (ISearch {}) = True
isExplicitStaging (IBindVar {}) = True
isExplicitStaging (IQuote {}) = True
isExplicitStaging (IQuoteName {}) = True
isExplicitStaging (IQuoteDecl {}) = True
isExplicitStaging (IRunElab {}) = True
isExplicitStaging _ = False

||| Insert a quotation or splice around the expression, if its type and
||| the current stage say we need one
export
insertStageCoercion : {vars : _} ->
                      {auto c : Ref Ctxt Defs} ->
                      {auto u : Ref UST UState} ->
                      NestedNames vars -> Env Term vars ->
                      RawImp -> Maybe (Glued vars) -> Core RawImp
insertStageCoercion nest env (IAlternative fc alt alts) exp
    = -- each alternative gets the coercions it needs
      pure (IAlternative fc alt !(traverse (\a => insertStageCoercion nest env a exp) alts))
insertStageCoercion nest env tm exp
    = if isExplicitStaging tm then pure tm else
      do defs <- get Ctxt
         -- Only if 'Code' or 'Low' is around at all
         False <- pure (isNothing !(lookupCtxtExact codeName (gamma defs)) &&
                        isNothing !(lookupCtxtExact lowName (gamma defs)))
              | True => pure tm
         st <- getStageState
         cur <- currentStage
         log "elab.stage" 10 $ "Considering " ++ show tm ++ " at stage " ++ show cur ++ " active " ++ show (active st)
         -- In types (stage checking not active), the base stage is the object
         -- level
         let cur' = if active st then cur else Just (fromMaybe SObj cur)
         let fc = getFC tm
         case cur' of
              Just SMeta =>
                 -- Code applied to arguments can't be meta level code: it's
                 -- object code, whatever the expected type is (e.g. the
                 -- argument of 'pure', which isn't known yet)
                 if !(codeApplied nest env tm)
                    then do log "elab.stage" 5 $ "Inserting quotation around " ++ show tm
                            pure (IStageQuote fc tm)
                    else
                 do Just expty <- pure exp
                         | Nothing => pure tm
                    Just _ <- isCodeNF !(getNF expty)
                         | Nothing => pure tm
                    if !(mustQuote nest env tm)
                       then do log "elab.stage" 5 $ "Inserting quotation around " ++ show tm
                               pure (IStageQuote fc tm)
                       else pure tm
              Just SObj =>
                 case !(needsSplice nest env tm exp) of
                      Just tm' =>
                         do log "elab.stage" 5 $ "Inserting splice: " ++ show tm'
                            pure tm'
                      Nothing => pure tm
              Nothing =>
                 -- The definition's stage isn't known yet. A meta level
                 -- application with a 'Code' result, checked against a type
                 -- which isn't 'Code', can only be object code.
                 do Just expty <- pure exp
                         | Nothing => pure tm
                    expnf <- getNF expty
                    case expnf of
                         NApp _ (NMeta {}) _ => pure tm -- don't know yet
                         _ => do Nothing <- isCodeNF expnf
                                      | Just _ => pure tm
                                 Just tm' <- needsSplice nest env tm exp
                                      | _ => pure tm
                                 log "elab.stage" 5 $ "Inserting splice: " ++ show tm'
                                 pure tm'
