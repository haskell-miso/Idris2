||| Two-level type theory, closure free code: compiling quotations of low code.
|||
||| A quotation [|| e ||] whose type is 'Low t' is elaborated as object code,
||| marked with 'Language.Staged.Low.lowQuote'. When the definition it is in
||| has been elaborated, this module translates it to the meta level code
||| that builds the representation of e ('LowExp', with higher order abstract
||| syntax binders), as MicroHs's lowQuoteExp does:
|||
|||  * lambdas and lets become HLam and HLet, with the meta level functions as
|||    binders, and the low types of the variables ('LowRep' search);
|||  * a constructor becomes HCon, a literal HLit, a primitive HPrim, a
|||    foreign function HForeign;
|||  * any other global function is unfolded: first by evaluation, with the
|||    object level arguments as variables (so that, e.g., interface methods
|||    become the primitives of their implementations), then, when it is stuck
|||    on object level values, by inlining its case tree. Case blocks and local
|||    functions are globals like this. A case on low code becomes HCase (or
|||    HCaseLit), and a recursive function becomes a local recursive function
|||    (HLetRec), so a recursive global is a first order loop;
|||  * a splice ~e (e : Low a) inserts e;
|||  * a variable of the definition that the low code is spliced into is HObj.
|||
||| Low code is first order: lambda bound variables have value types, and
||| functions are only called (with all their arguments, after 'reflect'
||| saturates the calls).
module TTImp.LowQuote

import Core.Case.CaseTree
import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.LowRep
import Core.Normalise
import Core.TT
import Core.Unify
import Core.UnifyState
import Core.Value

import TTImp.Elab.Stage

import Data.List

import Libraries.Data.List.SizeOf
import Libraries.Data.NameMap
import Libraries.Data.NatSet

%default covering

||| A more precise location, if it is in the same file (and not, e.g., in a
||| definition that is being inlined from another module)
refineFC : FC -> FC -> FC
refineFC new old
    = case (isConcreteFC old, isConcreteFC new) of
           (Just (o, _, _), Just (n, _, _)) => if o == n then new else old
           _ => old

||| Whether a function calls another, through functions in the namespace of
||| the other (its case blocks and local functions, and the functions of its
||| module)
reaches : {auto c : Ref Ctxt Defs} -> List Name -> Name -> Name -> Core Bool
reaches avoid from target = go avoid [from]
  where
    sameNS : Name -> Bool
    sameNS (NS ns _) = case target of
                            NS tns _ => ns == tns
                            _ => False
    sameNS _ = False

    go : List Name -> List Name -> Core Bool
    go seen [] = pure False
    go seen (n :: todo)
        = if n `elem` seen then go seen todo else
          do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => go (n :: seen) todo
             let Just refs = refersToM gdef
                  | Nothing => go (n :: seen) todo
             ns <- traverse toFullNames (keys refs)
             if target `elem` ns
                then pure True
                else go (n :: seen) (filter sameNS ns ++ todo)

||| The names of the variables in the patterns of a function's clauses: the
||| names of its arguments (when they are variables in the first clause), and
||| of the arguments of constructors by argument position (for names in the
||| generated code)
clausePatNames : {auto c : Ref Ctxt Defs} ->
                 GlobalDef -> Core (List (Maybe String), List (Nat, Name, List String))
clausePatNames gdef
    = case definition gdef of
           PMDef _ _ _ _ pats@(_ :: _) =>
               do cons <- traverse conNames pats
                  first <- case pats of
                                ((_ ** (_, lhs, _)) :: _) => pure (map varName (snd (getFnArgs lhs)))
                                [] => pure []
                  pure (first, concat cons)
           _ => pure ([], [])
  where
    varName : {vs : _} -> Term vs -> Maybe String
    varName (Local _ _ _ p)
        = let name = nameAt p in
              if isUserName name then Just (nameRoot name) else Nothing
    varName (As _ _ a _) = varName a
    varName _ = Nothing

    conArgs : {vs : _} -> Nat -> Term vs -> Core (List (Nat, Name, List String))
    conArgs i (As _ _ _ p) = conArgs i p
    conArgs i tm
        = case getFnArgs tm of
               (Ref _ (DataCon _ _) cn, as) =>
                   do cn' <- toFullNames cn
                      pure [(i, cn', map (fromMaybe "e" . varName) as)]
               _ => pure []

    conNames : (vs ** (Env Term vs, Term vs, Term vs)) -> Core (List (Nat, Name, List String))
    conNames (_ ** (_, lhs, _))
        = do let args = snd (getFnArgs lhs)
             concat <$> traverse (\(i, a) => conArgs i a) (zip [0 .. length args] args)

lookupNames : Nat -> Name -> List (Nat, Name, List String) -> Maybe (List String)
lookupNames i cn [] = Nothing
lookupNames i cn ((j, c, ns) :: rest)
    = if i == j && c == cn && any (/= "e") ns then Just ns else lookupNames i cn rest

||| The stage of a variable of the environment of a quotation
public export
data VarKind = VMeta | VObj
             | ||| An object level variable captured by a nested meta level
             ||| definition (e.g. a case block in a splice): it was bound in
             ||| a quotation of low code, so its value is low code (LowExp)
               VLowVar

||| The context of the translation of low code, in the environment (ws) of the
||| quotation
record LCtx (ws : Scope) where
  constructor MkLCtx
  fc : FC
  defining : Name
  env : Env Term ws
  ||| The stages of the variables in ws, innermost first
  kinds : List VarKind
  ||| Bound names standing for variables of low code (LowExp)
  lowVars : List Name
  ||| Bound names standing for (delayed) low code
  lazies : List (Name, Term ws)
  ||| Recursive globals being defined: the static arguments, and the
  ||| variable of low code for the specialised function
  recs : List (Name, List (Maybe (Term ws)), Name)
  ||| Unfolding depth, to stop at runaway unfolding
  depth : Nat
  ||| The names in the patterns of the function whose case tree is being
  ||| translated: its number of arguments, and for argument positions and
  ||| constructors, the names of the constructor's arguments
  patNames : (Nat, List (Nat, Name, List String))

lowErr : FC -> String -> Core a
lowErr fc msg = throw (GenericMsg fc ("low code: " ++ msg))

showName : {auto c : Ref Ctxt Defs} -> Name -> Core String
showName n = pure (show !(toFullNames n))

displayName : Name -> String
displayName n = nameRoot n

lowExpTy : {auto c : Ref Ctxt Defs} -> FC -> Core (Term vars)
lowExpTy fc = lref fc "LowExp"

lowListTy : {auto c : Ref Ctxt Defs} -> FC -> Core (Term vars)
lowListTy fc = pure (App fc !(globalRef fc (NS (mkNamespace "Prelude.Basics") (UN (Basic "List"))))
                            !(lowExpTy fc))

||| A lambda abstracting the bound name n (a variable of type a)
bindAs : FC -> Term ws -> Name -> Term ws -> Term ws
bindAs fc a n body = Bind fc n (Lam fc top Explicit a) (refsToLocals (Add n n None) body)

||| A meta level let binding the bound name n
letAs : FC -> Term ws -> Term ws -> Name -> Term ws -> Term ws
letAs fc a v n body = Bind fc n (Let fc top v a) (refsToLocals (Add n n None) body)

newBound : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           String -> Core Name
newBound root = genName ("lw" ++ root)

isLowVar : LCtx ws -> Name -> Bool
isLowVar ctx n = any (== n) (lowVars ctx)

lowVar : {ws : _} -> {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
         LCtx ws -> String -> Core (Name, LCtx ws)
lowVar ctx root
    = do n <- newBound root
         pure (n, { lowVars $= (n ::) } ctx)

-- Does a term (in the environment of the quotation) depend on low code, or
-- on object level variables? (Otherwise it is a meta level value.)
isDynamic : {ws : _} -> LCtx ws -> Term ws -> Bool
isDynamic ctx tm = dyn 0 tm
  where
    dyn : {vs : _} -> Nat -> Term vs -> Bool
    dyn under (Local _ _ idx _)
        = if idx < under then False
             else case getAt (minus idx under) (kinds ctx) of
                       Just VObj => True
                       Just VLowVar => True
                       _ => False
    dyn under (Ref _ Bound n) = isLowVar ctx n || isJust (lookup n (lazies ctx))
    dyn under (Meta _ _ _ args) = any (dyn under) args
    dyn under (Bind _ _ b sc) = dyn under (binderType b) || dyn (S under) sc ||
                                  (case b of
                                        Let _ _ v _ => dyn under v
                                        _ => False)
    dyn under (App _ f a) = dyn under f || dyn under a
    dyn under (As _ _ a p) = dyn under p
    dyn under (TDelayed _ _ t) = dyn under t
    dyn under (TDelay _ _ t a) = dyn under a
    dyn under (TForce _ _ t) = dyn under t
    dyn under (TQuote _ _ t) = dyn under t
    dyn under (TSplice _ t) = dyn under t
    dyn under _ = False

||| Is this a value type (first order data)?
isValueNF : {vars : _} -> {auto c : Ref Ctxt Defs} -> NF vars -> Core Bool
isValueNF (NBind _ _ (Pi {}) _) = pure False
isValueNF (NType {}) = pure False
isValueNF (NTCon _ n _ args)
    = if isCodeTyName !(toFullNames n)
         then pure False
         else -- the type arguments must be value types too (e.g. not
              -- Maybe (Low Int), or List (Int -> Int))
              do defs <- get Ctxt
                 allM (\a => isValueNF !(evalClosure defs (snd a))) args
  where
    allM : (a -> Core Bool) -> List a -> Core Bool
    allM p [] = pure True
    allM p (x :: xs) = if !(p x) then allM p xs else pure False
isValueNF _ = pure True

nfOf : {ws : _} -> {auto c : Ref Ctxt Defs} -> Env Term ws -> Term ws -> Core (NF ws)
nfOf env tm = do defs <- get Ctxt
                 nf defs env tm

showTy : {ws : _} -> {auto c : Ref Ctxt Defs} -> Env Term ws -> Term ws -> Core String
showTy env ty = do defs <- get Ctxt
                   pure (pretty False !(toFullNames !(normalise defs env ty)))
  where
    paren : Bool -> String -> String
    paren p s = if p then "(" ++ s ++ ")" else s

    -- a type, as in the source (without the namespaces, and the names of
    -- the arguments of non dependent function types)
    pretty : {vs : _} -> Bool -> Term vs -> String
    pretty p (Bind _ x (Pi _ _ _ a) sc)
        = let arg = pretty True a
              res = pretty False sc in
              paren p
                (if isUserName x && not (isMN x) then "(" ++ nameRoot x ++ " : " ++ arg ++ ") -> " ++ res
                 else arg ++ " -> " ++ res)
      where
        isMN : Name -> Bool
        isMN (MN _ _) = True
        isMN _ = False
    pretty p tm
        = case getFnArgs tm of
               (Ref _ _ n, []) => nameRoot n
               (Ref _ _ n, as) => paren p
                                    (concat (intersperse " " (nameRoot n :: map (pretty True) as)))
               (PrimVal _ c, []) => show c
               _ => show tm

||| The low type of a type
lowTy : {ws : _} -> {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
        LCtx ws -> Term ws -> Core (Term ws)
lowTy ctx ty = lowTyNF (fc ctx) (defining ctx) (env ctx) !(nfOf (env ctx) ty)

||| Check that a type is a value type
requireValue : {ws : _} -> {auto c : Ref Ctxt Defs} ->
               LCtx ws -> String -> Term ws -> Core ()
requireValue ctx what ty
    = do True <- isValueNF !(nfOf (env ctx) ty)
              | False => lowErr (fc ctx) (what ++ " must have a value type (first order data), not " ++
                                          !(showTy (env ctx) ty))
         pure ()

||| Check that a type is a low type: a value type, or a first order function
||| type (from value types)
requireLowTy : {ws : _} -> {auto c : Ref Ctxt Defs} ->
               LCtx ws -> String -> Term ws -> Core ()
requireLowTy ctx what ty = check !(nfOf (env ctx) ty)
  where
    check : NF ws -> Core ()
    check (NBind _ _ (Pi _ _ _ dom) sc)
        = do defs <- get Ctxt
             True <- isValueNF !(evalClosure defs dom)
                  | False => lowErr (fc ctx) (what ++ " must have a value type or a first order function type, not " ++
                                              !(showTy (env ctx) ty))
             check !(sc defs (toClosure defaultOpts (env ctx) (Erased (fc ctx) Placeholder)))
    check nf
        = do True <- isValueNF nf
                  | False => lowErr (fc ctx) (what ++ " must have a value type or a first order function type, not " ++
                                              !(showTy (env ctx) ty))
             pure ()

||| The literal of a constant, with its low type
lowLit : {ws : _} -> {auto c : Ref Ctxt Defs} -> FC -> Constant -> Core (Term ws)
lowLit fc c
    = case c of
           I i => lit "LitInt" (PrimVal fc (I i)) "TInt"
           BI i => lit "LitInteger" (PrimVal fc (BI i)) "TInteger"
           Db d => lit "LitDouble" (PrimVal fc (Db d)) "TDouble"
           Ch x => lit "LitChar" (PrimVal fc (Ch x)) "TChar"
           Str s => lit "LitString" (PrimVal fc (Str s)) "TString"
           I8 x => fixed "TInt8" (cast x)
           I16 x => fixed "TInt16" (cast x)
           I32 x => fixed "TInt32" (cast x)
           I64 x => fixed "TInt64" (cast x)
           B8 x => fixed "TBits8" (cast x)
           B16 x => fixed "TBits16" (cast x)
           B32 x => fixed "TBits32" (cast x)
           B64 x => fixed "TBits64" (cast x)
           _ => lowErr fc ("the constant " ++ show c ++ " cannot be used in low code")
  where
    lit : String -> Term ws -> String -> Core (Term ws)
    lit con v ty
        = pure (apps fc !(lref fc "HLit") [App fc !(lref fc con) v, !(lref fc ty)])

    fixed : String -> Integer -> Core (Term ws)
    fixed ty i
        = do t <- lref fc ty
             pure (apps fc !(lref fc "HLit") [apps fc !(lref fc "LitFixed") [t, PrimVal fc (BI i)], t])

||| The constructor of a literal of a variable (cross stage persistence of a
||| meta level value of a primitive type)
litOfVar : {ws : _} -> {auto c : Ref Ctxt Defs} ->
           FC -> NF ws -> Term ws -> Core (Maybe (Term ws))
litOfVar fc (NPrimVal _ (PrT t)) v
    = case t of
           IntType => lit "LitInt" "TInt"
           IntegerType => lit "LitInteger" "TInteger"
           DoubleType => lit "LitDouble" "TDouble"
           CharType => lit "LitChar" "TChar"
           StringType => lit "LitString" "TString"
           _ => pure Nothing
  where
    lit : String -> String -> Core (Maybe (Term ws))
    lit con ty
        = pure (Just (apps fc !(lref fc "HLit") [App fc !(lref fc con) v, !(lref fc ty)]))
litOfVar fc _ v = pure Nothing

||| The instantiation of a function or constructor type with some of its
||| arguments: the types of the other (run time) arguments, and the result
instTy : {ws : _} -> {auto c : Ref Ctxt Defs} ->
         FC -> Env Term ws -> NF ws -> List (Maybe (Term ws)) ->
         Core (List (Term ws), Term ws)
instTy fc env (NBind _ x (Pi _ rig _ dom) sc) (a :: as)
    = do defs <- get Ctxt
         rest <- sc defs (toClosure defaultOpts env (fromMaybe (Erased fc Placeholder) a))
         (ps, r) <- instTy fc env rest as
         case a of
              Just _ => pure (ps, r)
              Nothing => pure (!(quote defs env !(evalClosure defs dom)) :: ps, r)
instTy fc env nf _
    = do defs <- get Ctxt
         pure ([], !(quote defs env nf))

||| The static (Just: erased, implicit, or a meta level value at a type that
||| is not a value type) and dynamic (Nothing) arguments of an application of
||| a function or constructor of the given type
classify : {ws : _} -> {auto c : Ref Ctxt Defs} ->
           LCtx ws -> NF ws -> NatSet -> Nat -> List (Term ws) -> Core (List (Maybe (Term ws)))
classify ctx (NBind _ x (Pi _ rig pinfo dom) sc) erase pos (a :: as)
    = do defs <- get Ctxt
         rest <- sc defs (toClosure defaultOpts (env ctx) a)
         as' <- classify ctx rest erase (S pos) as
         let dynamic = isDynamic ctx a
         value <- isValueNF !(evalClosure defs dom)
         let static = isErased rig || elem pos erase || not (isExplicit pinfo) ||
                      (not dynamic && (not value || isMetaLocal a))
         pure ((if static then Just a else Nothing) :: as')
  where
    isExplicit : PiInfo t -> Bool
    isExplicit Explicit = True
    isExplicit _ = False

    isMetaLocal : Term ws -> Bool
    isMetaLocal (Local _ _ idx _)
        = case getAt idx (kinds ctx) of
               Just VMeta => True
               _ => False
    isMetaLocal _ = False
classify ctx _ erase pos as = pure (map (const Nothing) as)

||| The elements of a list at the positions where the other list has Nothing
dynOnly : List (Maybe b) -> List a -> List a
dynOnly (Nothing :: ms) (x :: xs) = x :: dynOnly ms xs
dynOnly (Just _ :: ms) (_ :: xs) = dynOnly ms xs
dynOnly _ _ = []

conAlts : List (CaseAlt ext) -> List (Name, (as : List Name ** CaseTree (as ++ ext)))
conAlts [] = []
conAlts (ConCase n _ as sc :: rest) = (n, (as ** sc)) :: conAlts rest
conAlts (_ :: rest) = conAlts rest

constAlts : List (CaseAlt ext) -> List (Constant, CaseTree ext)
constAlts [] = []
constAlts (ConstCase c sc :: rest) = (c, sc) :: constAlts rest
constAlts (_ :: rest) = constAlts rest

defaultAlts : List (CaseAlt ext) -> List (CaseTree ext)
defaultAlts [] = []
defaultAlts (DefaultCase sc :: rest) = sc :: defaultAlts rest
defaultAlts (_ :: rest) = defaultAlts rest

mkSubst : (vs : Scope) -> List (Term ws) -> Maybe (SubstEnv vs ws)
mkSubst [] _ = Just []
mkSubst (v :: vs) (t :: ts) = (t ::) <$> mkSubst vs ts
mkSubst _ _ = Nothing

appendSubst : SubstEnv as ws -> SubstEnv bs ws -> SubstEnv (as ++ bs) ws
appendSubst [] bs = bs
appendSubst (t :: ts) bs = t :: appendSubst ts bs

||| Make a list of low code
lowList : {auto c : Ref Ctxt Defs} -> FC -> List (Term ws) -> Core (Term ws)
lowList fc xs = mkList fc !(lowExpTy fc) xs

hApp : {auto c : Ref Ctxt Defs} -> FC -> Term ws -> List (Term ws) -> Core (Term ws)
hApp fc f [] = pure f
hApp fc f as = pure (apps fc !(lref fc "HApp") [f, !(lowList fc as)])

||| The constructor of the representation of a constructor
lowConRep : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core (Term ws)
lowConRep fc cn
    = do defs <- get Ctxt
         Just cdef <- lookupCtxtExact cn (gamma defs)
              | Nothing => lowErr fc ("unknown constructor " ++ show cn)
         let DCon tag ar nt = definition cdef
              | _ => lowErr fc (show cn ++ " is not a constructor")
         let rtArity = length [ i | i <- take ar [0 .. ar], not (elem i (eraseArgs cdef)) ]
         pure (apps fc !(lref fc "MkLowCon")
                  [ mkStr fc !(showName cn), PrimVal fc (I tag), !(mkNat fc rtArity),
                    !(mkBool fc (isJust nt)) ])

||| The representations of all the constructors of the type of a constructor
allConReps : {auto c : Ref Ctxt Defs} -> FC -> Name -> Core (List (Term ws))
allConReps fc cn
    = do defs <- get Ctxt
         Just cdef <- lookupCtxtExact cn (gamma defs)
              | Nothing => lowErr fc ("unknown constructor " ++ show cn)
         let (Ref _ _ tn, _) = getFnArgs (resultTy (type cdef))
              | _ => lowErr fc ("cannot find the type of " ++ show cn)
         Just tdef <- lookupCtxtExact tn (gamma defs)
              | Nothing => lowErr fc ("unknown type " ++ show tn)
         let TCon _ _ _ _ _ (Just cons) _ = definition tdef
              | _ => lowErr fc ("not a data type: " ++ show tn)
         traverse (lowConRep fc) cons
  where
    resultTy : Term vs -> Term vs
    resultTy (Bind _ _ (Pi {}) sc) = believe_me (resultTy sc)
    resultTy t = t

mutual
  ||| Translate low code (in the environment ext ++ ws, where the variables
  ||| ext are substituted by senv) to the meta level code that builds its
  ||| representation
  lowTm : {ext, ws : _} ->
          {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
          LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Term (ext ++ ws) -> Core (Term ws)
  lowTm ctx' sz senv tm
      = do -- errors are reported at the innermost term of the quotation
           let ctx = { fc $= refineFC (getLoc tm) } ctx'
           let fc = fc ctx
           case getFnArgs tm of
                (Bind bfc x (Lam _ _ _ ty) sc, args) =>
                    do lam <- lowLam ctx sz senv x ty sc
                       appArgs ctx sz senv lam args
                (Bind bfc x (Let _ _ val ty) sc, args) =>
                    do l <- lowLet ctx sz senv x val ty sc
                       appArgs ctx sz senv l args
                (Bind bfc x (Pi {}) sc, _) => lowErr fc "a type is not low code"
                (Local _ _ idx p, args) =>
                    do h <- lowLocal ctx sz senv idx p
                       appArgs ctx sz senv h args
                (Ref _ Bound n, args) =>
                    do h <- lowBound ctx n
                       appArgs ctx sz senv h args
                (Ref _ (DataCon _ _) n, args) => lowCon ctx sz senv n args
                (Ref _ (TyCon _) n, args) =>
                    lowErr fc ("the type " ++ !(showName n) ++ " is not low code")
                (Ref _ Func n, args) => lowGlobal ctx sz senv n args
                (TSplice _ e, args) =>
                    do h <- lowSplice ctx sz senv e
                       appArgs ctx sz senv h args
                (TDelay _ _ _ x, args) =>
                    do h <- lowTm ctx sz senv x
                       appArgs ctx sz senv h args
                (TForce _ _ x, args) =>
                    do h <- lowTm ctx sz senv x
                       appArgs ctx sz senv h args
                (PrimVal _ cst, []) => lowLit fc cst
                (Meta _ n _ _, _) => lowErr fc ("an unsolved hole " ++ !(showName n) ++ " in low code")
                (Erased _ _, _) => pure (App fc !(lref fc "HFail") (mkStr fc "erased"))
                (TQuote {}, _) => lowErr fc "a quotation is not low code"
                _ => lowErr fc "this term cannot be low code"

  appArgs : {ext, ws : _} ->
            {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
            LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Term ws -> List (Term (ext ++ ws)) ->
            Core (Term ws)
  appArgs ctx sz senv f [] = pure f
  appArgs ctx sz senv f args
      = hApp (fc ctx) f !(traverse (lowTm ctx sz senv) args)

  lowLam : {ext, ws : _} ->
           {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           LCtx ws -> SizeOf ext -> SubstEnv ext ws ->
           (x : Name) -> Term (ext ++ ws) -> Term (x :: ext ++ ws) -> Core (Term ws)
  lowLam ctx sz senv x ty sc
      = do let fc = fc ctx
           let ty' = substs sz senv ty
           requireValue ctx ("the lambda bound variable " ++ displayName x) ty'
           lty <- lowTy ctx ty'
           (v, ctx') <- lowVar ctx (displayName x)
           body <- lowTm ctx' (suc sz) (Ref fc Bound v :: senv) sc
           pure (apps fc !(lref fc "HLam")
                    [mkStr fc (displayName x), lty, bindAs fc !(lowExpTy fc) v body])

  lowLet : {ext, ws : _} ->
           {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           LCtx ws -> SizeOf ext -> SubstEnv ext ws ->
           (x : Name) -> Term (ext ++ ws) -> Term (ext ++ ws) -> Term (x :: ext ++ ws) -> Core (Term ws)
  lowLet ctx sz senv x val ty sc
      = do let fc = fc ctx
           let ty' = substs sz senv ty
           let sval = substs sz senv val
           value <- isValueNF !(nfOf (env ctx) ty')
           if not (isDynamic ctx sval) && not value
              then -- a meta level value (e.g. the value of a pattern
                   -- variable of a case block): substitute it
                   lowTm ctx (suc sz) (sval :: senv) sc
              else lowLetCode ctx sz senv x val ty' sc

  lowLetCode : {ext, ws : _} ->
               {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
               LCtx ws -> SizeOf ext -> SubstEnv ext ws ->
               (x : Name) -> Term (ext ++ ws) -> Term ws -> Term (x :: ext ++ ws) -> Core (Term ws)
  lowLetCode ctx sz senv x val ty' sc
      = do let fc = fc ctx
           requireLowTy ctx ("the let bound variable " ++ displayName x) ty'
           lty <- lowTy ctx ty'
           lty' <- mkJust fc !(lref fc "LowTy") lty
           val' <- lowTm ctx sz senv val
           (v, ctx') <- lowVar ctx (displayName x)
           body <- lowTm ctx' (suc sz) (Ref fc Bound v :: senv) sc
           pure (apps fc !(lref fc "HLet")
                    [mkStr fc (displayName x), lty', val', bindAs fc !(lowExpTy fc) v body])

  ||| A variable of the low code being translated
  lowLocal : {ext, ws : _} ->
             {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
             LCtx ws -> SizeOf ext -> SubstEnv ext ws ->
             (idx : Nat) -> (0 p : IsVar nm idx (ext ++ ws)) -> Core (Term ws)
  lowLocal ctx sz senv idx p
      = case locateVar sz (MkVar p) of
             Left v => lowEntry ctx (Var.index senv v)
             Right (MkVar {varIdx = i} q) => lowOuter ctx i q

  ||| A substituted variable: low code, delayed low code, or a static term
  lowEntry : {ws : _} ->
             {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
             LCtx ws -> Term ws -> Core (Term ws)
  lowEntry ctx (Ref fc Bound n) = lowBound ctx n
  lowEntry ctx t = lowTm ctx zero [] t

  lowBound : {ws : _} ->
             {auto c : Ref Ctxt Defs} ->
             LCtx ws -> Name -> Core (Term ws)
  lowBound ctx n
      = if isLowVar ctx n
           then pure (Ref (fc ctx) Bound n)
           else case lookup n (lazies ctx) of
                     Just t => pure t
                     Nothing => lowErr (fc ctx) ("internal error: unknown variable " ++ show n)

  ||| A variable of the environment of the quotation: an object level variable
  ||| of the definition the code is spliced into, or a meta level variable
  lowOuter : {ws : _} ->
             {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
             LCtx ws -> (i : Nat) -> (0 q : IsVar nm i ws) -> Core (Term ws)
  lowOuter ctx i q
      = do let fc = fc ctx
           let ty = binderType (getBinder q (env ctx))
           let v = Local fc Nothing i q
           let x = nameAt q
           case getAt i (kinds ctx) of
                Just VLowVar => pure v -- (its value is low code)
                Just VObj =>
                    do requireLowTy ctx ("the variable " ++ displayName x) ty
                       lty <- lowTy ctx ty
                       pure (apps fc !(lref fc "HObj") [mkStr fc (displayName x), lty, ty, v])
                _ => do Just l <- litOfVar fc !(nfOf (env ctx) ty) v
                             | Nothing => lowErr fc ("the meta level variable " ++ displayName x ++
                                                     " is used in low code (only a meta level value of a primitive type can be)")
                        pure l

  lowSplice : {ext, ws : _} ->
              {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
              LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Term (ext ++ ws) -> Core (Term ws)
  lowSplice ctx sz senv e
      = do let fc = fc ctx
           e' <- lowerMeta ctx False (substs sz senv e)
           pure (apps fc !(lref fc "lowExpOf") [Erased fc Placeholder, e'])

  ||| A constructor application
  lowCon : {ext, ws : _} ->
           {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Name -> List (Term (ext ++ ws)) ->
           Core (Term ws)
  lowCon ctx sz senv cn args
      = do let fc = fc ctx
           defs <- get Ctxt
           Just cdef <- lookupCtxtExact cn (gamma defs)
                | Nothing => lowErr fc ("unknown constructor " ++ show cn)
           let erase = eraseArgs cdef
           let args' = map (substs sz senv) args
           cty <- nf defs (env ctx) (embed (type cdef))
           let inst = zipWith (\i, a => if elem i erase then Just a else Nothing)
                              [0 .. length args] args'
           (ps, r) <- instTy fc (env ctx) cty (inst ++ restOf erase (length args) cty)
           traverse_ (requireValue ctx ("a field of " ++ !(showName cn))) ps
           lty <- if null ps then lowTy ctx r
                     else tFun fc !(traverse (lowTy ctx) ps) !(lowTy ctx r)
           rtargs <- traverse (lowTm ctx sz senv)
                         [ a | (i, a) <- zip [0 .. length args] args, not (elem i erase) ]
           pure (apps fc !(lref fc "HCon") [!(lowConRep fc cn), lty, !(lowList fc rtargs)])
    where
      -- The remaining (not applied) arguments: erased ones are instantiated
      -- with placeholders
      restOf : NatSet -> Nat -> NF ws -> List (Maybe (Term ws))
      restOf erase n (NBind _ _ (Pi {}) _)
          = map (\i => if elem i erase then Just (Erased (fc ctx) Placeholder) else Nothing)
                [n .. n + 50]
      restOf _ _ _ = []

  ||| An application of a global function
  lowGlobal : {ext, ws : _} ->
              {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
              LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Name -> List (Term (ext ++ ws)) ->
              Core (Term ws)
  lowGlobal ctx sz senv n args
      = do let fc = fc ctx
           defs <- get Ctxt
           Just gdef <- lookupCtxtExact n (gamma defs)
                | Nothing => lowErr fc ("unknown name " ++ show n)
           fname <- toFullNames (fullname gdef)
           if fname == lowLibName "lowQuote"
              then lowErr fc "a quotation is not low code"
              else lowDef ctx sz senv n fname gdef args

  lowDef : {ext, ws : _} ->
           {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Name -> Name -> GlobalDef ->
           List (Term (ext ++ ws)) -> Core (Term ws)
  lowDef ctx sz senv n fname gdef args
      = do let fc = fc ctx
           defs <- get Ctxt
           let args' = map (substs sz senv) args
           fty <- nf defs (env ctx) (embed (type gdef))
           cls <- classify ctx fty (eraseArgs gdef) 0 args'
           logC "elab.stage" 10 $ do
             as <- traverse toFullNames args'
             pure ("Low code: " ++ show fname ++ " applied to " ++ show as ++ " static " ++
                   show (map isJust cls) ++ " low variables " ++ show (lowVars ctx))
           case definition gdef of
                Builtin _ =>
                    do lty <- lowTy ctx (embed (type gdef))
                       dyn <- dynamicArgs cls
                       hApp fc (apps fc !(lref fc "HPrim") [mkStr fc (show fname), lty]) dyn
                ForeignDef _ ccs =>
                    do lty <- lowTy ctx (embed (type gdef))
                       dyn <- dynamicArgs cls
                       hApp fc (apps fc !(lref fc "HForeign")
                                    [mkStr fc (show fname), mkStr fc (cName ccs), lty]) dyn
                PMDef _ cargs treeCT _ _ =>
                    if depth ctx > 200
                       then lowErr fc ("unfolding " ++ show fname ++ " does not stop")
                       else case recCall (recs ctx) cls of
                                 Just fv => hApp fc (Ref fc Bound fv) !(dynamicArgs cls)
                                 Nothing => bindDynamic ({ depth $= S } ctx) cls [] $ \ctx', eargs =>
                                              unfold ctx' fname gdef cargs treeCT cls eargs
                _ => lowErr fc ("cannot use " ++ show fname ++ " in low code")
    where
      dynamicArgs : List (Maybe (Term ws)) -> Core (List (Term ws))
      dynamicArgs cls
          = traverse (lowTm ctx sz senv) (dynOnly cls args)

      sameStatic : List (Maybe (Term ws)) -> List (Maybe (Term ws)) -> Bool
      sameStatic [] [] = True
      sameStatic (Nothing :: xs) (Nothing :: ys) = sameStatic xs ys
      sameStatic (Just x :: xs) (Just y :: ys) = eqTerm x y && sameStatic xs ys
      sameStatic _ _ = False

      recCall : List (Name, List (Maybe (Term ws)), Name) -> List (Maybe (Term ws)) -> Maybe Name
      recCall [] _ = Nothing
      recCall ((f, st, v) :: rs) cls
          = if f == fname && sameStatic st cls then Just v else recCall rs cls

      cName : List String -> String
      cName [] = show fname
      cName (cc :: ccs)
          = case break (== ':') (unpack cc) of
                 (['C'], ':' :: rest) => pack (takeWhile (/= ',') rest)
                 _ => cName ccs

      -- Bind the dynamic arguments (translated) to variables of low code
      -- (call by value), or to delayed low code (lazy arguments, call by
      -- name), then continue with the arguments as terms
      bindDynamic : LCtx ws -> List (Maybe (Term ws)) -> List (Term ws) ->
                    (LCtx ws -> List (Term ws) -> Core (Term ws)) -> Core (Term ws)
      bindDynamic ctx' cls acc k = go ctx' (zip cls args) acc
        where
          go : LCtx ws -> List (Maybe (Term ws), Term (ext ++ ws)) -> List (Term ws) -> Core (Term ws)
          go c' [] acc = k c' (reverse acc)
          go c' ((Just s, _) :: rest) acc = go c' rest (s :: acc)
          go c' ((Nothing, a) :: rest) acc
              = do let fc = fc ctx
                   a' <- lowTm c' sz senv a
                   case a of
                        TDelay {} =>
                            do p <- newBound "lazy"
                               go ({ lazies $= ((p, a') ::) } c') rest (Ref fc Bound p :: acc)
                        _ => case a' of
                                  Ref _ Bound v => go c' rest (a' :: acc)
                                  _ => do (v, c'') <- lowVar c' "a"
                                          body <- go c'' rest (Ref fc Bound v :: acc)
                                          nothing <- mkNothing fc !(lref fc "LowTy")
                                          pure (apps fc !(lref fc "HLet")
                                                   [mkStr fc "a", nothing, a',
                                                    bindAs fc !(lowExpTy fc) v body])

  ||| Unfold a global function applied to arguments (static ones as terms,
  ||| dynamic ones as variables of low code)
  unfold : {ws : _} ->
           {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           LCtx ws -> Name -> GlobalDef -> (cargs : Scope) -> CaseTree cargs ->
           List (Maybe (Term ws)) -> List (Term ws) -> Core (Term ws)
  unfold ctx fname gdef cargs tree cls eargs
      = do let fc = fc ctx
           defs <- get Ctxt
           let app = apps fc (Ref fc Func fname) eargs
           res <- normaliseOpts withAll defs (env ctx) app
           if !(stuck res)
              then inline
              else lowTm ctx zero [] res
    where
      -- Evaluation is stuck in the function (or in a case block or local
      -- function of a recursive function, which calls it again)
      stuck : Term ws -> Core Bool
      stuck tm = case getFnArgs tm of
                      (Ref _ _ f, as) =>
                          do f' <- toFullNames f
                             if f' == fname
                                then pure (length as == length eargs)
                                else reaches (map fst (recs ctx)) f' fname
                      _ => pure False

      isRecursive : Core Bool
      -- (not counting the recursion through the functions which are being
      -- made local recursive functions: those calls are calls of them)
      isRecursive = reaches (map fst (recs ctx)) fname fname

      inline : Core (Term ws)
      inline
          = do let fc = fc ctx
               let (now, extra) = splitAt (length cargs) eargs
               let Just senv = mkSubst cargs now
                    | Nothing => lowErr fc ("the function " ++ show fname ++
                                            " is partially applied in low code")
               if !isRecursive
                  then letRec ctx fname gdef cargs tree cls eargs
                  else do (_, cons) <- clausePatNames gdef
                          res <- lowTree ({ patNames := (length cargs, cons) } ctx)
                                         (mkSizeOf cargs) senv tree
                          hApp fc res extra

  ||| A recursive global function, as a local recursive function of low code
  ||| (specialised to the static arguments)
  letRec : {ws : _} ->
           {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
           LCtx ws -> Name -> GlobalDef -> (cargs : Scope) -> CaseTree cargs ->
           List (Maybe (Term ws)) -> List (Term ws) -> Core (Term ws)
  letRec ctx fname gdef cargs tree cls eargs
      = do let fc = fc ctx
           defs <- get Ctxt
           fty <- nf defs (env ctx) (embed (type gdef))
           (ps, r) <- instTy fc (env ctx) fty cls
           traverse_ (requireValue ctx ("an argument of " ++ show fname)) ps
           lty <- tFun fc !(traverse (lowTy ctx) ps) !(lowTy ctx r)
           vs <- newBound "rec"
           (fv, ctx1) <- lowVar ctx (displayName fname)
           let ctx2 = { recs $= ((fname, cls, fv) ::) } ctx1
           -- The parameters: variables of low code for the dynamic arguments
           (params, ctx3) <- mkParams ctx2 cls
           let (now, extra) = splitAt (length cargs) params
           let Just senv = mkSubst cargs (map fst now)
                | Nothing => lowErr fc ("the function " ++ show fname ++ " is partially applied in low code")
           (argns, cons) <- clausePatNames gdef
           body <- lowTree ({ patNames := (length cargs, cons) } ctx3) (mkSizeOf cargs) senv tree
           let msk = the (List (Maybe ())) (map (\p => if isJust (snd p) then Nothing else Just ()) params)
           let dynParams = dynOnly msk (map fst params)
           let names = zipWith (\a, n => fromMaybe (displayName a) n)
                               (cargs ++ extraNames) (argns ++ replicate 50 Nothing)
           let dynNames = dynOnly msk names
           fun <- lams ctx3 (zip dynParams ps) (zip dynNames ps) body
           call <- hApp fc (Ref fc Bound fv) (dynOnly cls eargs)
           lexp <- lowExpTy fc
           llist <- lowListTy fc
           pair <- mkPair fc llist lexp !(lowList fc [fun]) call
           let fvdef = apps fc !(lref fc "lowNth") [!(mkNat fc 0), Ref fc Bound vs]
           tybind <- mkPair fc (PrimVal fc (PrT StringType)) !(lref fc "LowTy")
                            (mkStr fc (displayName fname)) lty
           decls <- mkList fc !(pairTy fc) [tybind]
           pure (apps fc !(lref fc "HLetRec")
                    [decls, bindAs fc llist vs (letAs fc lexp fvdef fv pair)])
    where
      extraNames : List Name
      extraNames = replicate 50 (UN (Basic "x"))

      pairTy : FC -> Core (Term ws)
      pairTy fc = pure (apps fc !(globalRef fc (NS (mkNamespace "Builtin") (UN (Basic "Pair"))))
                            [PrimVal fc (PrT StringType), !(lref fc "LowTy")])

      mkParams : LCtx ws -> List (Maybe (Term ws)) -> Core (List (Term ws, Maybe ()), LCtx ws)
      mkParams c' [] = pure ([], c')
      mkParams c' (Just s :: rest)
          = do (ps, c'') <- mkParams c' rest
               pure ((s, Nothing) :: ps, c'')
      mkParams c' (Nothing :: rest)
          = do (v, c1) <- lowVar c' "x"
               (ps, c2) <- mkParams c1 rest
               pure ((Ref (fc ctx) Bound v, Just ()) :: ps, c2)

      lams : LCtx ws -> List (Term ws, Term ws) -> List (String, Term ws) -> Term ws -> Core (Term ws)
      lams c' ((Ref _ Bound v, ty) :: rest) ((nm, _) :: nms) body
          = do let fc = fc ctx
               b <- lams c' rest nms body
               lty <- lowTy c' ty
               pure (apps fc !(lref fc "HLam") [mkStr fc nm, lty, bindAs fc !(lowExpTy fc) v b])
      lams c' _ _ body = pure body

  ||| Translate a case tree (of a function being unfolded)
  lowTree : {ext, ws : _} ->
            {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
            LCtx ws -> SizeOf ext -> SubstEnv ext ws -> CaseTree ext -> Core (Term ws)
  lowTree ctx sz senv (STerm _ tm) = lowTm ctx sz senv (embed tm)
  lowTree ctx sz senv (Unmatched msg)
      = pure (App (fc ctx) !(lref (fc ctx) "HFail") (mkStr (fc ctx) msg))
  lowTree ctx sz senv Impossible
      = pure (App (fc ctx) !(lref (fc ctx) "HFail") (mkStr (fc ctx) "impossible case"))
  lowTree ctx sz senv (Case idx p scTy alts)
      = do let fc = fc ctx
           let scr = Var.index senv (MkVar p)
           -- the position of the scrutinee among the function's arguments
           let (nargs, _) = patNames ctx
           let bound = minus (size sz) nargs
           let pos = if idx >= bound then Just (minus idx bound) else Nothing
           if isDynamic ctx scr
              then lowCase ctx sz senv !(lowEntry ctx scr) pos alts
              else staticCase ctx sz senv scr alts

  ||| A case on a value known at compile time: choose the alternative
  staticCase : {ext, ws : _} ->
               {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
               LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Term ws -> List (CaseAlt ext) ->
               Core (Term ws)
  staticCase ctx sz senv scr alts
      = do defs <- get Ctxt
           scnf <- nf defs (env ctx) scr
           case scnf of
                NDCon _ cn tag _ cargs =>
                    do cargs' <- traverse (\a => quote defs (env ctx) (snd a)) cargs
                       pick tag cargs' alts
                NPrimVal _ cst => pickConst cst alts
                _ => do tm <- quote defs (env ctx) scnf
                        what <- case tm of
                                     Local _ _ _ p =>
                                         let n = nameAt p in
                                             pure (if isUserName n then "the value of " ++ nameRoot n
                                                      else "an interface implementation")
                                     _ => pure (show !(toFullNames tm))
                        lowErr (fc ctx) (what ++ " is not known when the code is generated" ++
                                         " (low code is monomorphic)")
    where
      pick : Int -> List (Term ws) -> List (CaseAlt ext) -> Core (Term ws)
      pick tag cargs [] = lowErr (fc ctx) "no alternative matches a compile time value"
      pick tag cargs (ConCase _ t as sc :: rest)
          = if t == tag
               then case mkSubst as cargs of
                         Just fsub => lowTree ctx (mkSizeOf as + sz) (appendSubst fsub senv) sc
                         Nothing => lowErr (fc ctx) "a constructor with the wrong number of arguments"
               else pick tag cargs rest
      pick tag cargs (DefaultCase sc :: _) = lowTree ctx sz senv sc
      pick tag cargs (_ :: rest) = pick tag cargs rest

      pickConst : Constant -> List (CaseAlt ext) -> Core (Term ws)
      pickConst cst [] = lowErr (fc ctx) "no alternative matches a compile time value"
      pickConst cst (ConstCase c sc :: rest)
          = if c == cst then lowTree ctx sz senv sc else pickConst cst rest
      pickConst cst (DefaultCase sc :: _) = lowTree ctx sz senv sc
      pickConst cst (_ :: rest) = pickConst cst rest

  ||| A case on low code
  lowCase : {ext, ws : _} ->
            {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
            LCtx ws -> SizeOf ext -> SubstEnv ext ws -> Term ws -> Maybe Nat -> List (CaseAlt ext) ->
            Core (Term ws)
  lowCase ctx sz senv scr pos alts
      = do let fc = fc ctx
           let dflt = defaultAlts alts
           dflt' <- traverse (lowTree ctx sz senv) (take 1 dflt)
           case conAlts alts of
                cons@((cn, _) :: _) =>
                    do alts' <- traverse conAlt cons
                       allcs <- allConReps fc cn
                       contys <- lref fc "LowCon"
                       alttys <- lref fc "LowAlt"
                       d <- case dflt' of
                                 [d] => mkJust fc !(lowExpTy fc) d
                                 _ => mkNothing fc !(lowExpTy fc)
                       pure (apps fc !(lref fc "HCase")
                                [scr, !(mkList fc contys allcs), !(mkList fc alttys alts'), d])
                [] => do lalts <- traverse constAlt (constAlts alts)
                         d <- case dflt' of
                                   [d] => pure d
                                   _ => pure (App fc !(lref fc "HFail") (mkStr fc "no match"))
                         pairs <- mkList fc !(litPairTy fc) lalts
                         if null lalts
                            then pure d
                            else pure (apps fc !(lref fc "HCaseLit") [scr, pairs, d])
    where
      litPairTy : FC -> Core (Term ws)
      litPairTy fc = pure (apps fc !(globalRef fc (NS (mkNamespace "Builtin") (UN (Basic "Pair"))))
                              [!(lref fc "LowLit"), !(lowExpTy fc)])

      fields : LCtx ws -> Name -> NatSet -> Nat -> Nat -> List Name ->
               Core (List (Term ws), List (Name, Term ws), LCtx ws)
      fields c' vs erase pos rt [] = pure ([], [], c')
      fields c' vs erase pos rt (a :: as)
          = if elem pos erase
               then do (ts, bs, c'') <- fields c' vs erase (S pos) rt as
                       pure (Erased (fc ctx) Placeholder :: ts, bs, c'')
               else do (v, c1) <- lowVar c' (displayName a)
                       nth <- mkNat (fc ctx) rt
                       let get = apps (fc ctx) !(lref (fc ctx) "lowNth") [nth, Ref (fc ctx) Bound vs]
                       (ts, bs, c2) <- fields c1 vs erase (S pos) (S rt) as
                       pure (Ref (fc ctx) Bound v :: ts, (v, get) :: bs, c2)

      conAlt : (Name, (as : List Name ** CaseTree (as ++ ext))) -> Core (Term ws)
      conAlt (cn, (as ** sc))
          = do let fc = fc ctx
               defs <- get Ctxt
               cn' <- toFullNames cn
               -- the names of the fields in the source, if we know them
               let srcNames = case pos of
                                   Just i => lookupNames i cn' (snd (patNames ctx))
                                   Nothing => Nothing
               let argName = \i, a => fromMaybe (displayName a)
                                         (do ns <- srcNames
                                             guard (length ns == length as)
                                             getAt i ns)
               Just cdef <- lookupCtxtExact cn (gamma defs)
                    | Nothing => lowErr fc ("unknown constructor " ++ show cn)
               let erase = eraseArgs cdef
               vs <- newBound "fields"
               -- the run time fields are the variables of low code bound by
               -- the alternative (the n-th element of its argument list)
               (fieldTerms, binds, ctx') <- fields ctx vs erase 0 0
                                              (zipWith (\i, a => UN (Basic (argName i a))) [0 .. length as] as)
               let Just fsub = mkSubst as fieldTerms
                    | Nothing => lowErr fc "a constructor pattern with the wrong number of arguments"
               body <- lowTree ctx' (mkSizeOf as + sz) (appendSubst fsub senv) sc
               lexp <- lowExpTy fc
               let body' = foldr (\(v, i), b => letAs fc lexp i v b) body binds
               names <- mkList fc (PrimVal fc (PrT StringType))
                          [ mkStr fc (argName i a) | (i, a) <- zip [0 .. length as] as, not (elem i erase) ]
               pure (apps fc !(lref fc "MkLowAlt")
                        [!(lowConRep fc cn), names, bindAs fc !(lowListTy fc) vs body'])

      lowLitOnly : FC -> Constant -> Core (Term ws)
      lowLitOnly fc cst
          = case cst of
                 I i => pure (App fc !(lref fc "LitInt") (PrimVal fc (I i)))
                 BI i => pure (App fc !(lref fc "LitInteger") (PrimVal fc (BI i)))
                 Ch x => pure (App fc !(lref fc "LitChar") (PrimVal fc (Ch x)))
                 Str s => pure (App fc !(lref fc "LitString") (PrimVal fc (Str s)))
                 Db d => pure (App fc !(lref fc "LitDouble") (PrimVal fc (Db d)))
                 _ => lowErr fc ("a case on the constant " ++ show cst ++ " in low code")

      constAlt : (Constant, CaseTree ext) -> Core (Term ws)
      constAlt (cst, sc)
          = do let fc = fc ctx
               body <- lowTree ctx sz senv sc
               l <- lowLitOnly fc cst
               mkPair fc !(lref fc "LowLit") !(lowExpTy fc) l body

  ||| Translate the quotations of low code in a (meta level) term
  export
  lowerMeta : {ws : _} ->
              {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
              LCtx ws -> (object : Bool) -> Term ws -> Core (Term ws)
  lowerMeta ctx object tm
      = case getFnArgs tm of
             (Ref fc _ f, [ty, TQuote qfc _ body]) =>
                 if !(toFullNames f) == lowLibName "lowQuote"
                    then do e <- lowTm ({ fc $= refineFC qfc } ctx) zero [] body
                            pure (apps fc !(lref fc "MkLow") [ty, e])
                    else go tm
             (Ref fc _ f, [nm, lty, ty, Ref _ Bound v]) =>
                 -- an object level variable of a definition that has been
                 -- inlined into low code is a variable of the low code
                 if !(toFullNames f) == lowLibName "HObj" && isLowVar ctx v
                    then pure (Ref fc Bound v)
                    else go tm
             _ => go tm
    where
      extend : Binder (Term ws) -> LCtx ws -> LCtx (x :: ws)
      extend b c' = MkLCtx (fc c') (defining c') (b :: env c')
                           ((if object then VObj else VMeta) :: kinds c')
                           (lowVars c') [] [] (depth c') (0, [])

      go : Term ws -> Core (Term ws)
      go (Bind fc x b sc)
          = do b' <- traverse (lowerMeta ctx object) b
               sc' <- lowerMeta (extend b ctx) object sc
               pure (Bind fc x b' sc')
      go (App fc f a) = pure (App fc !(lowerMeta ctx object f) !(lowerMeta ctx object a))
      go (TQuote fc ty body) = pure (TQuote fc ty !(lowerMeta ctx True body))
      go (TSplice fc e) = pure (TSplice fc !(lowerMeta ctx False e))
      go (TDelay fc r ty a) = pure (TDelay fc r ty !(lowerMeta ctx object a))
      go (TForce fc r a) = pure (TForce fc r !(lowerMeta ctx object a))
      go (TDelayed fc r a) = pure (TDelayed fc r !(lowerMeta ctx object a))
      go t = pure t

||| Does a term mention the given (resolved) name?
mentions : Name -> Term vs -> Bool
mentions n (Ref _ _ m) = n == m
mentions n (Meta _ _ _ args) = any (mentions n) args
mentions n (Bind _ _ b sc)
    = mentions n (binderType b) || mentions n sc ||
      case b of
           Let _ _ v _ => mentions n v
           _ => False
mentions n (App _ f a) = mentions n f || mentions n a
mentions n (As _ _ a p) = mentions n p
mentions n (TDelayed _ _ t) = mentions n t
mentions n (TDelay _ _ t a) = mentions n a
mentions n (TForce _ _ t) = mentions n t
mentions n (TQuote _ _ t) = mentions n t
mentions n (TSplice _ t) = mentions n t
mentions n _ = False

||| Translate the quotations of low code in the right hand side of a clause.
||| The stages of the pattern variables: those of the definition, or of the
||| named variables of a nested definition.
export
lowerClause : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST UState} ->
              FC -> Name -> Bool -> NameMap Stage -> Clause -> Core Clause
lowerClause fc def metaDef varStages (MkClause env lhs rhs)
    = do defs <- get Ctxt
         let lq = lowLibName "lowQuote"
         Just _ <- lookupCtxtExact lq (gamma defs)
              | Nothing => pure (MkClause env lhs rhs)
         let lqr = maybe lq Resolved (getNameID lq (gamma defs))
         if not (mentions lqr rhs || mentions lq rhs)
            then pure (MkClause env lhs rhs)
            else do rhs' <- normaliseHoles defs env rhs
                    let ctx = MkLCtx fc def env (kindsOf env) [] [] [] 0 (0, [])
                    rhs'' <- lowerMeta ctx (not metaDef) rhs'
                    log "elab.stage" 5 $ "Low code translated in " ++ show def
                    pure (MkClause env lhs rhs'')
  where
    -- a case block renames a captured variable that a pattern rebinds (to
    -- MN x i, see TTImp.Elab.Case): then the name is the pattern's
    shadowed : List Name -> Name -> Bool
    shadowed all n = renamedIn varStages all n

    kindsOf : {vs : _} -> Env Term vs -> List VarKind
    kindsOf env = go (toList vs) env
      where
        go : {vs' : _} -> List Name -> Env Term vs' -> List VarKind
        go all {vs' = []} [] = []
        go all {vs' = x :: xs} (b :: bs)
            = (case (if shadowed all x then Nothing else capturedStage varStages x) of
                    Just SMeta => VMeta
                    Just SObj => if metaDef then VLowVar else VObj
                    Nothing => if metaDef then VMeta else VObj) :: go all bs
