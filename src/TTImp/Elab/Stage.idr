||| Two-level type theory: stage checking during elaboration.
|||
||| Every term is either at the meta level (run at compile time) or at the
||| object level (run at run time). Quotations [|| e ||] move from the meta
||| level to the object level, and splices ~e move back. Global definitions
||| have a stage (a 'Staged' flag), or are stage polymorphic. Local variables
||| have the stage at which they were bound.
|||
||| The stage of a definition is fixed by its type (meta if the type mentions
||| 'Code'), or by what its body uses: a quotation, or a meta level name,
||| makes it meta; a splice makes it object level. A definition which uses
||| neither is stage polymorphic.
module TTImp.Elab.Stage

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import Libraries.Data.NameMap

%default covering

export
getStageState : {auto u : Ref UST UState} -> Core StageState
getStageState = stageState <$> get UST

export
putStageState : {auto u : Ref UST UState} -> StageState -> Core ()
putStageState s = update UST { stageState := s }

export
updateStageState : {auto u : Ref UST UState} ->
                   (StageState -> StageState) -> Core ()
updateStageState f = update UST { stageState $= f }

||| The current stage, if it is known
export
currentStage : {auto u : Ref UST UState} -> Core (Maybe Stage)
currentStage
    = do st <- getStageState
         case frames st of
              ((_, s) :: _) => pure (Just s)
              [] => pure (base st)

stageText : Stage -> String
stageText SMeta = "the meta level (compile time)"
stageText SObj = "the object level (run time)"

hint : Stage -> Stage -> String
hint SMeta SObj = "\nUse a splice ~(...) to run it and insert the code it produces."
hint SObj SMeta = "\nUse a quotation [|| ... ||] to make object level code."
hint _ _ = ""

stageMismatch : FC -> String -> (needed : Stage) -> (actual : Stage) -> Error
stageMismatch fc what needed actual
    = GenericMsg fc (what ++ " is at " ++ stageText needed ++
                     ", but it is used at " ++ stageText actual ++ "." ++
                     hint needed actual)

||| Require the current stage to be 's', fixing the stage of the definition
||| being elaborated if it is not known yet.
export
requireStage : {auto u : Ref UST UState} ->
               FC -> Lazy String -> Stage -> Core ()
requireStage fc what s
    = do st <- getStageState
         when (active st) $
           case frames st of
                ((_, s') :: _) =>
                    unless (s == s') $ throw (stageMismatch fc what s s')
                [] => case base st of
                           Nothing => putStageState ({ base := Just s } st)
                           Just s' => unless (s == s') $
                                         throw (stageMismatch fc what s s')

-- The stage of the local variable at the given position (from the outside)
-- of the environment
varStageAt : Name -> (pos : Nat) -> StageState -> Maybe Stage
varStageAt n pos st = findFrame (frames st)
  where
    findFrame : List (Nat, Stage) -> Maybe Stage
    findFrame ((len, s) :: fs)
        = if len <= pos then Just s else findFrame fs
    findFrame []
        = case lookup n (baseVars st) of
               Just s => Just s
               Nothing => base st

||| The stage of the local variable 'n' with the given de Bruijn index
export
localStage : {auto u : Ref UST UState} ->
             (vars : Scope) -> Name -> (idx : Nat) -> Core (Maybe Stage)
localStage vars n idx
    = do st <- getStageState
         pure (varStageAt n (minus (length vars) (S idx)) st)

||| Check that a local variable is used at the stage it was bound at.
||| Uses in erased positions (e.g. types in object code) are always fine,
||| since staging computes them and they don't exist at run time.
||| Meta level values of primitive types (Int, String, ...) can be used
||| directly at the object level (cross stage persistence), since staging
||| turns them into literals.
export
checkLocalStage : {auto u : Ref UST UState} ->
                  FC -> RigCount -> (vars : Scope) -> Name -> (idx : Nat) ->
                  (isPrimTy : Core Bool) -> Core ()
checkLocalStage fc rig vars n idx isPrimTy
    = do st <- getStageState
         when (active st && not (isErased rig)) $
           do Just vs <- localStage vars n idx
                   | Nothing => pure () -- bound at the (unknown) base stage
              Just cur <- currentStage
                   | Nothing => requireStage fc ("The variable " ++ show n) vs
              when (vs /= cur) $
                 do -- cross stage persistence for primitive values
                    prim <- isPrimTy
                    unless (vs == SMeta && cur == SObj && prim) $
                       requireStage fc ("The variable " ++ show n) vs

||| Record the stages for a nested definition (case block or local function)
||| created here, which captures the variables in the environment
export
registerNested : {auto u : Ref UST UState} ->
                 {vars : _} ->
                 Name -> Env Term vars -> Core ()
registerNested n env
    = do st <- getStageState
         when (active st) $
           do body <- currentStage
              let outer = reverse vars -- outermost first
              let stages = zipWith (\p, x => varStageAt x p st)
                                   [0 .. length outer] outer
              let named = fromList (mapMaybe (\ (x, s) => map (x,) s)
                                             (zip outer stages))
              putStageState ({ nested $= insert n (body, named, stages) } st)

||| Check that a global name is used at a stage where it exists
export
checkGlobalStage : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   FC -> GlobalDef -> Core ()
checkGlobalStage fc def
    = do st <- getStageState
         when (active st) $
           case defStage def of
                Nothing => pure ()
                Just DMeta =>
                    requireStage fc ("The meta level definition " ++ show !(toFullNames def.fullname)) SMeta
                Just DObj =>
                    requireStage fc ("The object level definition " ++ show !(toFullNames def.fullname)) SObj
                Just (DMixed _) =>
                    requireStage fc ("The object level definition " ++ show !(toFullNames def.fullname)) SObj

||| Run an elaborator inside a quotation (stage SObj) or a splice (SMeta),
||| starting at the given environment length
export
inStage : {auto u : Ref UST UState} ->
          (envlen : Nat) -> Stage -> Core a -> Core a
inStage len s act
    = do st <- getStageState
         let fs = frames st
         putStageState ({ frames := (len, s) :: fs } st)
         res <- catch act (\err => do updateStageState { frames := fs }
                                      throw err)
         updateStageState { frames := fs }
         pure res

||| Run an elaborator with stage checking switched off (e.g. for types)
export
noStageCheck : {auto u : Ref UST UState} -> Core a -> Core a
noStageCheck act
    = do st <- getStageState
         putStageState ({ active := False } st)
         res <- catch act (\err => do updateStageState { active := active st }
                                      throw err)
         updateStageState { active := active st }
         pure res

||| Remember the current quotation/splice frames, to restore them when running
||| a delayed elaborator
export
saveFrames : {auto u : Ref UST UState} -> Core (List (Nat, Stage))
saveFrames = frames <$> getStageState

export
withFrames : {auto u : Ref UST UState} -> List (Nat, Stage) -> Core a -> Core a
withFrames fs act
    = do st <- getStageState
         putStageState ({ frames := fs } st)
         res <- catch act (\err => do updateStageState { frames := frames st }
                                      throw err)
         updateStageState { frames := frames st }
         pure res

||| Does a term mention 'Code', other than inside a splice? (A type that does
||| is a meta level type.)
export
mentionsCode : Term vars -> Bool
mentionsCode (Ref _ _ n) = n == codeName
mentionsCode (Meta _ _ _ args) = any mentionsCode args
mentionsCode (Bind _ _ b sc)
    = mentionsCode (binderType b) || mentionsCode sc ||
      case b of
           Let _ _ v _ => mentionsCode v
           _ => False
mentionsCode (App _ f a) = mentionsCode f || mentionsCode a
mentionsCode (As _ _ _ p) = mentionsCode p
mentionsCode (TDelayed _ _ t) = mentionsCode t
mentionsCode (TDelay _ _ t a) = mentionsCode t || mentionsCode a
mentionsCode (TForce _ _ t) = mentionsCode t
mentionsCode (TQuote _ _ _) = False -- the type of a quotation is not a type annotation
mentionsCode (TSplice _ _) = False -- an object level type computed by a splice
mentionsCode _ = False

||| Is this the type of a meta level definition? It is if it mentions 'Code',
||| perhaps after unfolding type synonyms.
export
isMetaType : {vars : _} ->
             {auto c : Ref Ctxt Defs} -> Env Term vars -> Term vars -> Core Bool
isMetaType env ty
    = if mentionsCode ty
         then pure True
         else do defs <- get Ctxt
                 -- Only bother normalising if 'Code' exists at all
                 Just _ <- lookupCtxtExact codeName (gamma defs)
                      | Nothing => pure False
                 nty <- normalise defs env ty
                 pure (mentionsCode nty)

||| Add a stage flag to a definition
export
setStage : {auto c : Ref Ctxt Defs} ->
           FC -> Name -> DefStage -> Core ()
setStage fc n s
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact n (gamma defs)
              | Nothing => pure ()
         let flags' = Staged s :: filter (not . isStaged) gdef.flags
         ignore $ addDef n ({ flags := flags' } gdef)
  where
    isStaged : DefFlag -> Bool
    isStaged (Staged _) = True
    isStaged _ = False
