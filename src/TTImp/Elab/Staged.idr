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

||| Is the name the 'Code' type constructor?
export
isCodeName : {auto c : Ref Ctxt Defs} -> Name -> Core Bool
isCodeName n
    = do n' <- getFullName n
         pure (n' == codeName)

||| If the given normal form is 'Code a', return 'a'
export
isCodeNF : {auto c : Ref Ctxt Defs} ->
           {vars : _} -> NF vars -> Core (Maybe (Closure vars))
isCodeNF (NTCon _ n _ [(_, a)])
    = if !(isCodeName n) then pure (Just a) else pure Nothing
isCodeNF _ = pure Nothing

newTypeMeta : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              FC -> Env Term vars -> String -> Core (Term vars)
newTypeMeta fc env root
    = do nm <- genName root
         u <- uniVar fc
         metaVar fc erased env nm (TType fc u)

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
         -- If we know the expected type is 'Code a', check the body against 'a'
         expty <- the (Core (Maybe (Term vars))) $ case exp of
                       Nothing => pure Nothing
                       Just gexp =>
                          do Just a <- isCodeNF !(getNF gexp)
                                  | Nothing => pure Nothing
                             anf <- evalClosure defs a
                             pure (Just !(quote defs env anf))
         aty <- case expty of
                     Nothing => newTypeMeta fc env "quoteTy"
                     Just t => pure t
         (tm', gty) <- inStage (length vars) SObj $
                         check rig elabinfo nest env tm (Just (gnf env aty))
         ty <- getTerm gty
         cty <- mkCodeType fc ty
         checkExp rig elabinfo env fc (TQuote fc ty tm')
                  (gnf env cty) exp

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
         cty <- mkCodeType fc aty
         (tm', _) <- inStage (length vars) SMeta $
                       check rig elabinfo nest env tm (Just (gnf env cty))
         pure (TSplice fc tm', gnf env aty)

||| Is this an application of the 'Code' type constructor to an argument?
export
isCodeApp : {auto c : Ref Ctxt Defs} ->
            RawImp -> Core (Maybe (FC, RawImp))
isCodeApp (IApp fc (IVar vfc n) arg)
    = do defs <- get Ctxt
         Just _ <- lookupCtxtExact codeName (gamma defs)
              | Nothing => pure Nothing
         [(_, _, gdef)] <- lookupCtxtName n (gamma defs)
              | _ => pure Nothing
         if !(getFullName gdef.fullname) == codeName
            then pure (Just (fc, arg))
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
               FC -> RawImp -> Maybe (Glued vars) ->
               Core (Term vars, Glued vars)
checkCodeApp rig elabinfo nest env fc arg exp
    = do requireStage fc "The type 'Code'" SMeta
         u <- uniVar fc
         (argtm, _) <- inStage (length vars) SObj $
                         check erased elabinfo nest env arg (Just (gType fc u))
         cty <- mkCodeType fc argtm
         u' <- uniVar fc
         checkExp rig elabinfo env fc cty (gType fc u') exp
