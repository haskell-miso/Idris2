||| Two-level type theory: elaboration of quotations and splices.
|||
|||   [|| e ||] : Code a     if e : a at the object level  (a meta level value)
|||   ~e        : a          if e : Code a at the meta level (an object level term)
|||
||| with the definitional equalities ~[|| e ||] = e and [|| ~e ||] = e.
module TTImp.Elab.Staged

import Core.Env
import Core.Metadata
import Core.Unify
import Core.Value

import Idris.REPL.Opts
import Idris.Syntax

import TTImp.Elab.Check
import TTImp.Elab.Delayed
import TTImp.Elab.Stage
import TTImp.TTImp

%default covering

||| Staged code needs 'Language.Staged.Code' to be defined
export
requireCode : {auto c : Ref Ctxt Defs} -> FC -> Core ()
requireCode fc
    = do defs <- get Ctxt
         Just _ <- lookupCtxtExact codeName (gamma defs)
              | Nothing => throw (GenericMsg fc "Staged code needs the type 'Code': import Language.Staged")
         pure ()

||| Closure free code needs 'Language.Staged.Low.Low' to be defined
export
requireLow : {auto c : Ref Ctxt Defs} -> FC -> Core ()
requireLow fc
    = do defs <- get Ctxt
         Just _ <- lookupCtxtExact lowName (gamma defs)
              | Nothing => throw (GenericMsg fc "Closure free code needs the type 'Low': import Language.Staged.Low")
         pure ()

||| Is the name a type constructor of object code ('Code' or 'Low')?
export
isCodeName : {auto c : Ref Ctxt Defs} -> Name -> Core Bool
isCodeName n
    = do n' <- getFullName n
         pure (isCodeTyName n')

||| If the given normal form is 'Code a' or 'Low a', return whether it is
||| 'Low', and 'a'
export
codeKindNF : {auto c : Ref Ctxt Defs} ->
             {vars : _} -> NF vars -> Core (Maybe (Bool, Closure vars))
codeKindNF (NTCon _ n _ [(_, a)])
    = do n' <- getFullName n
         pure (if n' == codeName then Just (False, a)
               else if n' == lowName then Just (True, a)
               else Nothing)
codeKindNF _ = pure Nothing

||| If the given normal form is 'Code a' or 'Low a', return 'a'
export
isCodeNF : {auto c : Ref Ctxt Defs} ->
           {vars : _} -> NF vars -> Core (Maybe (Closure vars))
isCodeNF nf = map snd <$> codeKindNF nf

||| The type of object code of the given kind (True: Low)
export
mkCodeKindType : {auto c : Ref Ctxt Defs} -> Bool -> FC -> Term vars -> Core (Term vars)
mkCodeKindType low = if low then mkLowType else mkCodeType

newTypeMeta : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Env Term vars -> String -> Core (Term vars)
newTypeMeta fc env root
    = do nm <- genName root
         u <- uniVar fc
         metaVar fc erased env nm (TType fc u)

checkStageQuoteWith : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  {auto e : Ref EST (EState vars)} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  RigCount -> ElabInfo ->
                  NestedNames vars -> Env Term vars ->
                  FC -> RawImp -> Maybe (Glued vars) ->
                  Core (Term vars, Glued vars)
checkStageQuoteWith rig elabinfo nest env fc tm exp
    = do defs <- get Ctxt
         -- If we know the expected type is 'Code a' or 'Low a', check the
         -- body against 'a'. A quotation is closure free code (Low) if its
         -- expected type is 'Low a', and Code otherwise.
         kind <- the (Core (Maybe (Bool, Term vars))) $ case exp of
                       Nothing => pure Nothing
                       Just gexp =>
                          do Just (low, a) <- codeKindNF !(getNF gexp)
                                  | Nothing => pure Nothing
                             anf <- evalClosure defs a
                             pure (Just (low, !(quote defs env anf)))
         let low = maybe False fst kind
         when low $ requireLow fc
         aty <- case kind of
                     Nothing => newTypeMeta fc env "quoteTy"
                     Just (_, t) => pure t
         (tm', gty) <- inQuoteKind low $ inStage (length vars) SObj $
                         check rig elabinfo nest env tm (Just (gnf env aty))
         ty <- getTerm gty
         if low
            then -- marked, and translated to the representation of low code
                 -- when the definition has been elaborated (TTImp.LowQuote)
                 do lty <- mkLowType fc ty
                    lq <- lowLibRef fc "lowQuote"
                    checkExp rig elabinfo env fc
                             (App fc (App fc lq ty) (TQuote fc ty tm'))
                             (gnf env lty) exp
            else do cty <- mkCodeType fc ty
                    checkExp rig elabinfo env fc (TQuote fc ty tm')
                             (gnf env cty) exp

export
checkStageQuote : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref MD Metadata} ->
                  {auto u : Ref UST UState} ->
                  {auto e : Ref EST (EState vars)} ->
                  {auto s : Ref Syn SyntaxInfo} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  RigCount -> ElabInfo ->
                  NestedNames vars -> Env Term vars ->
                  FC -> RawImp -> Maybe (Glued vars) ->
                  Core (Term vars, Glued vars)
checkStageQuote rig elabinfo nest env fc tm exp
    = do requireCode fc
         requireStage fc "A quotation [|| ... ||]" SMeta
         defs <- get Ctxt
         lowLoaded <- isJust <$> lookupCtxtExact lowName (gamma defs)
         case exp of
              Just gexp =>
                  -- If the expected type isn't known yet, we don't know if
                  -- the quotation is Code or Low: wait until it is known
                  if lowLoaded && !(unknown !(getNF gexp))
                     then delayOnFailure fc rig env exp isKindErr QuoteKind $ \delayed =>
                            if delayed
                               then do e <- getTerm gexp
                                       checkStageQuoteWith rig elabinfo nest env fc tm (Just (gnf env e))
                               else throw (GenericMsg fc kindMsg)
                     else -- If the type depends on code which can't be computed
                          -- yet (a splice on an unsolved hole), try again later
                          delayOnFailure fc rig env exp stuckSplice QuoteKind $ \delayed =>
                            if delayed
                               then do e <- getTerm gexp
                                       checkStageQuoteWith rig elabinfo nest env fc tm (Just (gnf env e))
                               else checkStageQuoteWith rig elabinfo nest env fc tm exp
              Nothing => checkStageQuoteWith rig elabinfo nest env fc tm exp
  where
    hasSplice : Term vs -> Bool
    hasSplice (TSplice _ _) = True
    hasSplice (App _ f a) = hasSplice f || hasSplice a
    hasSplice (Bind _ _ b sc) = hasSplice (binderType b) || hasSplice sc
    hasSplice (TQuote _ _ t) = hasSplice t
    hasSplice _ = False

    stuckSplice : Error -> Bool
    stuckSplice (CantConvert _ _ _ x y) = hasSplice x || hasSplice y
    stuckSplice (CantSolveEq _ _ _ x y) = hasSplice x || hasSplice y
    stuckSplice (WhenUnifying _ _ _ x y err) = hasSplice x || hasSplice y || stuckSplice err
    stuckSplice _ = False

    kindMsg : String
    kindMsg = "The kind of the quotation is not known yet"

    unknown : NF vars -> Core Bool
    unknown (NApp _ (NMeta {}) _) = pure True
    unknown _ = pure False

    isKindErr : Error -> Bool
    isKindErr (GenericMsg _ msg) = msg == kindMsg
    isKindErr _ = False


isCodeTm : {auto c : Ref Ctxt Defs} -> Term vs -> Core Bool
isCodeTm tm = case getFn tm of
                   Ref _ _ n => pure (!(toFullNames n) == codeName)
                   _ => pure False

-- Whether a type error is a mismatch with Code
isCodeErr : {auto c : Ref Ctxt Defs} -> Error -> Core Bool
isCodeErr (CantConvert _ _ _ x y) = pure (!(isCodeTm x) || !(isCodeTm y))
isCodeErr (CantSolveEq _ _ _ x y) = pure (!(isCodeTm x) || !(isCodeTm y))
isCodeErr (WhenUnifying _ _ _ x y err)
    = pure (!(isCodeTm x) || !(isCodeTm y) || !(isCodeErr err))
isCodeErr (InRHS _ _ err) = isCodeErr err
isCodeErr _ = pure False

export
checkStageSplice : {vars : _} ->
                   {auto c : Ref Ctxt Defs} ->
                   {auto m : Ref MD Metadata} ->
                   {auto u : Ref UST UState} ->
                   {auto e : Ref EST (EState vars)} ->
                   {auto s : Ref Syn SyntaxInfo} ->
                   {auto o : Ref ROpts REPLOpts} ->
                   RigCount -> ElabInfo ->
                   NestedNames vars -> Env Term vars ->
                   FC -> RawImp -> Maybe (Glued vars) ->
                   Core (Term vars, Glued vars)
checkStageSplice rig elabinfo nest env fc tm exp
    = do requireCode fc
         requireStage fc "A splice ~(...)" SObj
         updateStageState { usedSplice := True }
         aty <- maybe (newTypeMeta fc env "spliceTy") getTerm exp
         if !inLowQuote
            then -- only closure free code can be spliced into closure free code
                 do cty <- mkLowType fc aty
                    (tm', _) <- handle
                                  (inStage (length vars) SMeta $
                                     check rig elabinfo nest env tm (Just (gnf env cty)))
                                  (\err => do notLow <- isCodeErr err
                                              if notLow
                                                 then throw (GenericMsg fc "Only Low code can be spliced into low code")
                                                 else throw err)
                    pure (TSplice fc tm', gnf env aty)
            else -- object code, or a Code quotation: the code can be Code or
                 -- Low (closure free code is ordinary code)
                 do (tm', gty) <- inStage (length vars) SMeta $
                                    check rig elabinfo nest env tm Nothing
                    kind <- codeKindNF !(getNF gty)
                    cty <- mkCodeKindType (maybe False fst kind) fc aty
                    (tm'', _) <- checkExp rig elabinfo env fc tm' gty (Just (gnf env cty))
                    pure (TSplice fc tm'', gnf env aty)

||| Is this an application of the 'Code' or 'Low' type constructor to an
||| argument? (And is it 'Low'?)
export
isCodeApp : {auto c : Ref Ctxt Defs} ->
            RawImp -> Core (Maybe (FC, RawImp, Bool))
isCodeApp (IApp fc (IVar vfc n) arg)
    = do defs <- get Ctxt
         False <- pure (isNothing !(lookupCtxtExact codeName (gamma defs)) &&
                        isNothing !(lookupCtxtExact lowName (gamma defs)))
              | True => pure Nothing
         [(_, _, gdef)] <- lookupCtxtName n (gamma defs)
              | _ => pure Nothing
         fn <- getFullName gdef.fullname
         if isCodeTyName fn
            then pure (Just (fc, arg, fn == lowName))
            else pure Nothing
isCodeApp _ = pure Nothing

||| 'Code a' is a meta level type, and 'a' is an object level type, so check
||| 'a' at the object level
export
checkCodeApp : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto m : Ref MD Metadata} ->
               {auto u : Ref UST UState} ->
               {auto e : Ref EST (EState vars)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               RigCount -> ElabInfo ->
               NestedNames vars -> Env Term vars ->
               FC -> RawImp -> Bool -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkCodeApp rig elabinfo nest env fc arg low exp
    = do requireStage fc (if low then "The type 'Low'" else "The type 'Code'") SMeta
         u <- uniVar fc
         (argtm, _) <- inStage (length vars) SObj $
                         check erased elabinfo nest env arg (Just (gType fc u))
         cty <- mkCodeKindType low fc argtm
         u' <- uniVar fc
         checkExp rig elabinfo env fc cty (gType fc u') exp
