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
|||   variable, or an application whose head cannot return code (its result
|||   is another type constructor, or a type variable constrained by an
|||   interface, as in 'x * y'). Meta level code with a 'Code' result is
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
data ResultKind = RCode | RVar | RConcrete | RUnknown

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
    go : Nat -> Bool -> NF vars -> Core (ResultKind, Bool)
    go k cons (NBind fc x (Pi _ _ Explicit aty) sc)
        = case k of
               Z => pure (RConcrete, cons) -- a function is not code
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
    go (S _) cons _ = pure (RUnknown, cons)
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

-- Can this expression, checked against 'Code a' at the meta level, not have
-- that type as it is? Then it's object code, and needs quoting.
mustQuote : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            NestedNames vars -> Env Term vars -> RawImp -> Core Bool
mustQuote nest env (IPrimVal _ _) = pure True
mustQuote nest env (ILam {}) = pure True
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
                  pure (info.isCodeVal && nargs > 0)
              Nothing =>
                  case info.result of
                       RCode => pure False
                       RConcrete => pure True
                       RVar => pure info.constrained
                       RUnknown => pure False

-- Is this a meta level expression with a 'Code' result, used at the object
-- level? Then it needs splicing (Left), or its head does (Right)
needsSplice : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              NestedNames vars -> Env Term vars -> RawImp ->
              Core (Maybe (Either () ()))
needsSplice nest env tm
    = do let (hd, nargs) = getHead tm Z
         Just info <- headInfo nest env hd nargs
              | Nothing => pure Nothing
         case info.stage of
              Just SMeta =>
                 if info.isCodeVal && nargs > 0
                    then pure (Just (Right ()))
                    else case info.result of
                              RCode => pure (Just (Left ()))
                              _ => pure Nothing
              _ => pure Nothing

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
insertStageCoercion nest env tm exp
    = if isExplicitStaging tm then pure tm else
      do defs <- get Ctxt
         -- Only if 'Code' is around at all
         Just _ <- lookupCtxtExact codeName (gamma defs)
              | Nothing => pure tm
         st <- getStageState
         cur <- currentStage
         log "elab.stage" 10 $ "Considering " ++ show tm ++ " at stage " ++ show cur ++ " active " ++ show (active st)
         -- In types (stage checking not active), the base stage is the object
         -- level
         let cur' = if active st then cur else Just (fromMaybe SObj cur)
         let fc = getFC tm
         case cur' of
              Just SMeta =>
                 do Just expty <- pure exp
                         | Nothing => pure tm
                    Just _ <- isCodeNF !(getNF expty)
                         | Nothing => pure tm
                    if !(mustQuote nest env tm)
                       then do log "elab.stage" 5 $ "Inserting quotation around " ++ show tm
                               pure (IStageQuote fc tm)
                       else pure tm
              Just SObj =>
                 case !(needsSplice nest env tm) of
                      Just (Left ()) =>
                         do log "elab.stage" 5 $ "Inserting splice around " ++ show tm
                            pure (IUnquote fc tm)
                      Just (Right ()) =>
                         do let (hd, _) = getHead tm Z
                            log "elab.stage" 5 $ "Inserting splice around the head of " ++ show tm
                            pure (replaceHead (IUnquote (getFC hd) hd) tm)
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
                                 Just (Left ()) <- needsSplice nest env tm
                                      | _ => pure tm
                                 log "elab.stage" 5 $ "Inserting splice around " ++ show tm
                                 requireStage fc "A splice" SObj
                                 pure (IUnquote fc tm)
