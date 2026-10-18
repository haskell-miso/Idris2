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

-- The key recording that a case block may rename a captured variable x (at
-- index i of the environment) to MN x i, when a pattern rebinds x
export
renameKey : String -> Int -> Name
renameKey x i = MN ("rename:" ++ x) i

||| Is the name a variable bound by a pattern of a case block, which rebinds a
||| captured variable of the same name (which the case block renames, see
||| TTImp.Elab.Case)?
export
renamedIn : NameMap a -> List Name -> Name -> Bool
renamedIn captured vars (UN un)
    = any (\v => case v of
                       MN y i => y == displayUserName un &&
                                 isJust (lookup (renameKey y i) captured) &&
                                 -- (and not a variable of that name that
                                 -- an outer case block renamed)
                                 isNothing (lookup v captured)
                       _ => False) vars
renamedIn _ _ _ = False

||| The stage of a captured variable, by its name in a nested definition
export
capturedStage : NameMap a -> Name -> Maybe a
capturedStage captured n@(MN y i)
    = case lookup n captured of
           Just s => Just s
           Nothing => lookup (renameKey y i) captured
capturedStage captured n = lookup n captured

-- 'captured' says whether the variable can be one captured by a nested
-- definition (whose stages are in baseVars): not if it shadows another
-- variable of the same name
varStageAtIn : (captured : Bool) -> Name -> (pos : Nat) -> StageState -> Maybe Stage
varStageAtIn captured n pos st = findFrame (frames st)
  where
    findFrame : List (Nat, Stage) -> Maybe Stage
    findFrame ((len, s) :: fs)
        = if len <= pos then Just s else findFrame fs
    findFrame []
        = case (if captured then capturedStage (baseVars st) n else Nothing) of
               Just s => Just s
               Nothing => base st



-- The stage of the local variable at the given position (from the outside)
-- of the environment
varStageAt : Name -> (pos : Nat) -> StageState -> Maybe Stage
varStageAt n pos st = varStageAtIn True n pos st



||| The stage of the local variable 'n' with the given de Bruijn index
export
localStage : {auto u : Ref UST UState} ->
             (vars : Scope) -> Name -> (idx : Nat) -> Core (Maybe Stage)
localStage vars n idx
    = do st <- getStageState
         let pos = minus (length vars) (S idx)
         -- the outermost variable of this name is the captured one
         let first = firstPos 0 (reverse (toList vars))
         -- a case block renames a captured variable that a pattern rebinds
         -- (to MN x i, see TTImp.Elab.Case): then the name is the pattern's
         pure (varStageAtIn (not (renamedIn (baseVars st) (toList vars) n) &&
                             maybe True (== pos) first) n pos st)
  where
    firstPos : Nat -> List Name -> Maybe Nat
    firstPos i [] = Nothing
    firstPos i (x :: xs) = if x == n then Just i else firstPos (S i) xs

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
              -- the names of the variables, and the names they get in a
              -- case block where a pattern rebinds them (TTImp.Elab.Case)
              let inner = reverse (zip outer stages)
              let renamed = concat $ mapMaybe (\ (i, (x, s)) =>
                                         case x of
                                              UN un => map (\s' => [(renameKey (displayUserName un) (cast i), s')]) s
                                              _ => Nothing)
                                     (zip [0 .. length inner] inner)
              let named = fromList (mapMaybe (\ (x, s) => map (x,) s)
                                             (zip outer stages) ++ renamed)
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
Frames : Type
Frames = (List (Nat, Stage), List Bool)

export
saveFrames : {auto u : Ref UST UState} -> Core Frames
saveFrames = do st <- getStageState
                pure (frames st, quoteKinds st)

export
withFrames : {auto u : Ref UST UState} -> Frames -> Core a -> Core a
withFrames (fs, qs) act
    = do st <- getStageState
         putStageState ({ frames := fs, quoteKinds := qs } st)
         res <- catch act (\err => do updateStageState { frames := frames st,
                                                         quoteKinds := quoteKinds st }
                                      throw err)
         updateStageState { frames := frames st, quoteKinds := quoteKinds st }
         pure res

||| Run an elaborator inside a quotation of the given kind (True: Low)
export
inQuoteKind : {auto u : Ref UST UState} -> Bool -> Core a -> Core a
inQuoteKind low act
    = do st <- getStageState
         let qs = quoteKinds st
         putStageState ({ quoteKinds := low :: qs } st)
         res <- catch act (\err => do updateStageState { quoteKinds := qs }
                                      throw err)
         updateStageState { quoteKinds := qs }
         pure res

||| Is the innermost quotation we are in a quotation of closure free code?
export
inLowQuote : {auto u : Ref UST UState} -> Core Bool
inLowQuote = do st <- getStageState
                pure (case quoteKinds st of
                           (b :: _) => b
                           [] => False)

||| Does a term mention 'Code', other than inside a splice? (A type that does
||| is a meta level type.)
export
mentionsCode : Term vars -> Bool
mentionsCode (Ref _ _ n) = isCodeTyName n
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
    = do defs <- get Ctxt
         -- Only if 'Code' or 'Low' exists at all
         False <- pure (isNothing !(lookupCtxtExact codeName (gamma defs)) &&
                        isNothing !(lookupCtxtExact lowName (gamma defs)))
              | True => pure False
         if mentionsCode !(toFullNames ty)
            then pure True
            else do nty <- normalise defs env ty
                    pure (mentionsCode !(toFullNames nty))

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
