||| A code generator from low code to C, as an example of a user written
||| backend for Language.Staged.Low.  Since low code is first order, strict,
||| and monomorphic, the translation is direct:
|||
|||  * Int, Integer (as int64_t, so it can overflow), the fixed width types,
|||    Double, Char are C scalars, and a String is a const char*;
|||  * a data type whose constructors have no fields is an int (the tag);
|||  * other data types are structs with a tag and a union of the fields,
|||    allocated with malloc (and never freed: this example has no memory
|||    management);
|||  * the tags are named by an enum per data type, Type_Con (e.g. Bool_True);
|||  * local functions (let and letrec bound lambdas) become C functions; the
|||    variables of the enclosing scope they use are passed as extra
|||    arguments (lambda lifting), which is always possible since functions
|||    never escape;
|||  * a case is a switch (or a chain of ifs, on strings and doubles), a let
|||    is a declaration.
|||
||| The entry point is toC; the generated program has a function with the
||| given name that takes the free variables (and the parameters, if the
||| program is a function) and returns the result.
module Language.Staged.Low.C

import Data.List
import Data.Maybe
import Data.String
import Language.Staged.Low

%default covering

-- The output: function definitions (in reverse order), the statements of the
-- current function (in reverse order), a counter for fresh names, and the
-- names used by the program
record CS where
  constructor MkCS
  csFuns : List String
  csStmts : List String
  csUniq : Nat
  csUsed : List String

record C a where
  constructor MkC
  unC : CS -> (a, CS)

Functor C where
  map f (MkC g) = MkC $ \s => let (a, s') = g s in (f a, s')

Applicative C where
  pure a = MkC $ \s => (a, s)
  MkC f <*> MkC a = MkC $ \s => let (g, s') = f s
                                    (b, s'') = a s' in (g b, s'')

Monad C where
  MkC g >>= f = MkC $ \s => let (a, s') = g s in unC (f a) s'

emit : String -> C ()
emit l = MkC $ \s => ((), { csStmts $= (l ::) } s)

addFun : String -> C ()
addFun f = MkC $ \s => ((), { csFuns $= (f ::) } s)

-- Run the statements of a function body (or a branch) in a fresh buffer
block : C a -> C (a, List String)
block act = MkC $ \s =>
  let (a, s') = unC act ({ csStmts := [] } s) in
      ((a, reverse (csStmts s')), { csStmts := csStmts s } s')

--------------------------------------------------------------------------
-- Names

||| A C identifier for a name of the program
export
cName : String -> String
cName = concatMap esc . unpack . baseName
  where
    esc : Char -> String
    esc c = if isAlphaNum c && ord c < 128 then singleton c
            else case c of
                      '_' => "_"
                      '(' => "T"
                      ')' => ""
                      ',' => "c"
                      '[' => "L"
                      ']' => "ist"
                      ':' => "Cons"
                      '\'' => "_q"
                      _ => "_" ++ show (ord c) ++ "_"

fresh : String -> C String
fresh b = MkC $ \s =>
  let n = pick (csUsed s) (csUniq s) (length (csUsed s) + 1) in
      (b ++ "_" ++ show n, { csUniq := S n } s)
  where
    -- the first number that doesn't make a name of the program (the fuel is
    -- enough: there are only so many names)
    pick : List String -> Nat -> Nat -> Nat
    pick used i Z = i
    pick used i (S k) = if (b ++ "_" ++ show i) `elem` used then pick used (S i) k else i

--------------------------------------------------------------------------
-- Types

isEnum : LowDecl -> Bool
isEnum d = all (null . conDeclFields) (declCons d)

||| The C type of a value type
export
cType : LowTy -> String
cType TInt = "int64_t"
cType TInteger = "int64_t"
cType TInt8 = "int8_t"
cType TInt16 = "int16_t"
cType TInt32 = "int32_t"
cType TInt64 = "int64_t"
cType TBits8 = "uint8_t"
cType TBits16 = "uint16_t"
cType TBits32 = "uint32_t"
cType TBits64 = "uint64_t"
cType TDouble = "double"
cType TChar = "uint32_t"
cType TString = "const char*"
cType (TData n _ d) = if isEnum d then "int" else "struct " ++ cName n ++ "*"
cType _ = "void*"   -- never happens: functions are not values

-- The name of the tag of a constructor: Type_Con
tagName : LowDecl -> String -> String
tagName d c = cName (declName d) ++ "_" ++ cName c

-- The tag of a constructor (of a value of the type), as an enum constant
conTagName : LowTy -> LowCon -> String
conTagName (TData _ _ d) c = tagName d (conName c)
conTagName _ c = show (conTag c)

-- The declaration of a data type: an enum that names its tags, and (when it
-- isn't an enumeration) a struct.  For simplicity, the fields whose types
-- are parameters are void*.
cDecl : LowDecl -> String
cDecl d
    = if isEnum d then tags
         else tags ++ "\n" ++
              "struct " ++ cName (declName d) ++ " { int tag; union { " ++
              concat [ "struct { " ++
                       concat [ cType (param t) ++ " f" ++ show i ++ "; "
                              | (i, t) <- zip [0 .. length (conDeclFields c)] (conDeclFields c) ] ++
                       "} " ++ cName (conDeclName c) ++ "; "
                     | c <- declCons d, not (null (conDeclFields c)) ] ++
              "} u; };"
  where
    param : LowTy -> LowTy
    param (TParam _) = TOther "void*"
    param t = t

    tags : String
    tags = "enum { " ++
           joinBy ", " [ tagName d (conDeclName c) ++ " = " ++ show (conDeclTag c)
                       | c <- declCons d ] ++ " };"

--------------------------------------------------------------------------
-- Literals and primitives

cString : String -> String
cString s = "\"" ++ concatMap esc (unpack s) ++ "\""
  where
    esc : Char -> String
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = if ord c < 32 || ord c > 126
               then "\\" ++ pad (octal (ord c))
               else singleton c
      where
        octal : Int -> String
        octal n = if n < 8 then show n else assert_total (octal (n `div` 8)) ++ show (n `mod` 8)

        pad : String -> String
        pad o = replicate (minus 3 (length o)) '0' ++ o

cLit : LowLit -> String
cLit (LitInt i) = show i
cLit (LitInteger i) = show i
cLit (LitDouble d) = show d
cLit (LitChar c) = show (ord c)
cLit (LitString s) = cString s
cLit (LitFixed _ i) = show i

-- prim__add_Int is ("add", "Int")
primParts : String -> Maybe (String, String)
primParts p
    = case break (== '_') (unpack (fromMaybe p (stripPrefix "prim__" p))) of
           (op, '_' :: ty) => if isPrefixOf "prim__" p then Just (pack op, pack ty) else Nothing
           _ => Nothing
  where
    stripPrefix : String -> String -> Maybe String
    stripPrefix pre s = if isPrefixOf pre s then Just (substr (length pre) (length s) s) else Nothing

-- The C type named by the type part of a primitive's name
primCType : String -> String
primCType "Int" = "int64_t"
primCType "Integer" = "int64_t"
primCType "Int8" = "int8_t"
primCType "Int16" = "int16_t"
primCType "Int32" = "int32_t"
primCType "Int64" = "int64_t"
primCType "Bits8" = "uint8_t"
primCType "Bits16" = "uint16_t"
primCType "Bits32" = "uint32_t"
primCType "Bits64" = "uint64_t"
primCType "Double" = "double"
primCType "Char" = "uint32_t"
primCType t = "/* " ++ t ++ " */ int64_t"

-- The primitives of the runtime system that low code can use
prim : String -> List String -> String
prim p as
    = case (primParts p, as) of
           (Just (op, ty), [a, b]) =>
               case lookup op binops of
                    Just o => bin o a b
                    Nothing => unknown
           (Just ("neg", _), [a]) => "(-" ++ a ++ ")"
           (Just ("cast", tys), [a]) =>
               -- prim__cast_IntDouble: the type to cast to is the second
               case [ t | t <- castTypes, isSuffixOf t tys, t /= tys ] of
                    (t :: _) => "((" ++ primCType t ++ ")" ++ a ++ ")"
                    [] => unknown
           _ => case (p, as) of
                     ("prim__doubleExp", [a]) => "exp(" ++ a ++ ")"
                     ("prim__doubleLog", [a]) => "log(" ++ a ++ ")"
                     ("prim__doubleSin", [a]) => "sin(" ++ a ++ ")"
                     ("prim__doubleCos", [a]) => "cos(" ++ a ++ ")"
                     ("prim__doubleTan", [a]) => "tan(" ++ a ++ ")"
                     ("prim__doubleSqrt", [a]) => "sqrt(" ++ a ++ ")"
                     ("prim__doubleFloor", [a]) => "floor(" ++ a ++ ")"
                     ("prim__doubleCeiling", [a]) => "ceil(" ++ a ++ ")"
                     ("prim__doublePow", [a, b]) => "pow(" ++ a ++ ", " ++ b ++ ")"
                     _ => unknown
  where
    bin : String -> String -> String -> String
    bin o a b = "(" ++ a ++ " " ++ o ++ " " ++ b ++ ")"

    binops : List (String, String)
    binops = [ ("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/"), ("mod", "%")
             , ("lt", "<"), ("lte", "<="), ("eq", "=="), ("gte", ">="), ("gt", ">")
             , ("shl", "<<"), ("shr", ">>"), ("and", "&"), ("or", "|"), ("xor", "^") ]

    castTypes : List String
    castTypes = [ "Integer", "Int8", "Int16", "Int32", "Int64", "Int"
                , "Bits8", "Bits16", "Bits32", "Bits64", "Double", "Char" ]

    unknown : String
    unknown = "/* unknown primitive " ++ p ++ " */ " ++ cName p ++ "(" ++ joinBy ", " as ++ ")"

--------------------------------------------------------------------------
-- Code generation

-- Is a field of a constructor of a type one whose type is a parameter (and
-- so is a void* in the struct)?
isParamField : LowTy -> LowCon -> Nat -> Bool
isParamField (TData _ _ decl) c i
    = case find (\cd => conDeclTag cd == conTag c) (declCons decl) of
           Just cd => case getAt i (conDeclFields cd) of
                           Just (TParam _) => True
                           _ => False
           Nothing => False
isParamField _ _ _ = False

-- A value from or to a void* field (a pointer or an integer is stored in
-- it, a double with the helper functions in the program)
fromField : Bool -> LowTy -> String -> String
fromField False _ e = e
fromField True TDouble e = "void2double(" ++ e ++ ")"
fromField True t@(TData _ _ d) e
    = if isEnum d then "((int)(intptr_t)" ++ e ++ ")" else "((" ++ cType t ++ ")" ++ e ++ ")"
fromField True t e = "((" ++ cType t ++ ")(intptr_t)" ++ e ++ ")"

toField : Bool -> LowTy -> String -> String
toField False _ e = e
toField True TDouble e = "double2void(" ++ e ++ ")"
toField True (TData _ _ d) e = if isEnum d then "((void*)(intptr_t)" ++ e ++ ")" else e
toField True _ e = "((void*)(intptr_t)" ++ e ++ ")"

-- The environment: the variables in scope with their types, and the lifted
-- functions with the variables they capture
record Env where
  constructor MkEnv
  eVars : List (String, LowTy)
  eFuns : List (String, List (String, LowTy))

addVars : List (String, LowTy) -> Env -> Env
addVars xs = { eVars $= (xs ++) }

addFunCaps : String -> List (String, LowTy) -> Env -> Env
addFunCaps f caps = { eFuns $= ((f, caps) ::) }

indentLines : List String -> String
indentLines = concatMap (\l => "  " ++ l ++ "\n")

nubVars : List (String, LowTy) -> List (String, LowTy)
nubVars = nubBy (\a, b => fst a == fst b)

isFun : LowTy -> Bool
isFun (TFun _ _) = True
isFun _ = False

-- Functions are lambda lifted to C functions.  The captured variables are
-- the free variables of the body that are bound in the environment (except
-- functions), and the variables captured by the functions it calls.
capturedOf : Env -> LowTerm -> List (String, LowTy)
capturedOf env e
    = nubVars (concatMap captured (freeVars e))
  where
    captured : (String, LowTy) -> List (String, LowTy)
    captured (v, _)
        = case lookup v (eVars env) of
               Just t => if isFun t then fromMaybe [] (lookup v (eFuns env)) else [(v, t)]
               Nothing => fromMaybe [] (lookup v (eFuns env))

funSig : String -> LowTy -> List (String, LowTy) -> LowTerm -> String
funSig x (TFun _ r) caps (LLam xs _)
    = "static " ++ cType r ++ " " ++ cName x ++ "(" ++
      joinBy ", " [ cType pt ++ " " ++ cName p | (p, pt) <- caps ++ xs ] ++ ")"
funSig x _ _ _ = "static void " ++ cName x ++ "(void)"

mutual
  -- gen returns a C expression for the value of the term, after emitting the
  -- statements that compute it
  gen : Env -> LowTerm -> C String
  gen env (LVar x _) = pure (cName x)
  gen env (LLit l _) = pure (cLit l)
  gen env (LPrim p _) = pure (cName p)
  gen env (LForeign _ c _) = pure c
  gen env (LApp f as)
      = do as' <- traverse (gen env) as
           case f of
                LPrim p _ => pure (prim p as')
                LForeign _ c _ => pure (c ++ "(" ++ joinBy ", " as' ++ ")")
                LVar g _ =>
                    -- a call of a local function: pass the captured variables too
                    let caps = map (cName . fst) (fromMaybe [] (lookup g (eFuns env))) in
                        pure (cName g ++ "(" ++ joinBy ", " (caps ++ as') ++ ")")
                _ => pure "/* bad call */ 0"
  gen env (LLam _ _) = pure "/* lambda */ 0"
  gen env (LLet x t e b)
      = if isFun t
           then do let caps = capturedOf env e
                   let env' = addFunCaps x caps (addVars [(x, t)] env)
                   defineFun env' x caps e
                   gen env' b
           else do e' <- gen env e
                   emit (cType t ++ " " ++ cName x ++ " = " ++ e' ++ ";")
                   gen (addVars [(x, t)] env) b
  gen env (LLetRec bs b)
      = do -- all the functions of the group capture the same variables
           let caps = nubVars (concatMap (\(_, _, e) => capturedOf env e) bs)
           let env' = foldr (\(x, _, _) => addFunCaps x caps)
                            (addVars (map (\(x, t, _) => (x, t)) bs) env) bs
           -- prototypes first, so that the functions can call each other
           traverse_ (\(x, t, e) => addFun (funSig x t caps e ++ ";")) bs
           traverse_ (\(x, _, e) => defineFun env' x caps e) bs
           gen env' b
  gen env tm@(LCase s cons alts d)
      = do s' <- gen env s
           let st = typeOf s
           r <- fresh "r"
           emit (cType (typeOf tm) ++ " " ++ r ++ ";")
           case (st, alts) of
                (TData _ _ decl, [(_, [(x, t)], b)]) =>
                    if declNewtype decl
                       then do emit (cType t ++ " " ++ cName x ++ " = " ++ s' ++ ";")
                               b' <- gen (addVars [(x, t)] env) b
                               emit (r ++ " = " ++ b' ++ ";")
                       else switch st decl s' r
                (TData _ _ decl, _) => switch st decl s' r
                _ => emit ("/* case on " ++ show st ++ " */")
           pure r
    where
      alt : LowTy -> String -> String -> (LowCon, List (String, LowTy), LowTerm) -> C ()
      alt st s' r (c, xs, b)
          = do emit ("case " ++ conTagName st c ++ ": {")
               traverse_ (\(i, (x, t)) =>
                            emit (cType t ++ " " ++ cName x ++ " = " ++
                                  fromField (isParamField st c i) t
                                     (s' ++ "->u." ++ cName (conName c) ++ ".f" ++ show i) ++ ";"))
                         (zip [0 .. length xs] xs)
               (b', ss) <- block (gen (addVars xs env) b)
               traverse_ emit ss
               emit (r ++ " = " ++ b' ++ "; break; }")

      switch : LowTy -> LowDecl -> String -> String -> C ()
      switch st decl s' r
          = do emit ("switch (" ++ (if isEnum decl then s' else s' ++ "->tag") ++ ") {")
               traverse_ (alt st s' r) alts
               case d of
                    Just e => if length alts < length cons
                                 then do emit "default: {"
                                         (e', ss) <- block (gen env e)
                                         traverse_ emit ss
                                         emit (r ++ " = " ++ e' ++ "; break; }")
                                 else emit "default: abort();"
                    Nothing => emit "default: abort();"   -- all constructors are covered
               emit "}"
  gen env tm@(LCaseLit s alts d)
      = do s' <- gen env s
           let st = typeOf s
           r <- fresh "r"
           emit (cType (typeOf tm) ++ " " ++ r ++ ";")
           case st of
                TString => ifs r (\l => "strcmp(" ++ s' ++ ", " ++ cLit l ++ ") == 0")
                TDouble => ifs r (\l => s' ++ " == " ++ cLit l)
                _ => do emit ("switch (" ++ s' ++ ") {")
                        traverse_ (\(l, b) =>
                                     do emit ("case " ++ cLit l ++ ": {")
                                        (b', ss) <- block (gen env b)
                                        traverse_ emit ss
                                        emit (r ++ " = " ++ b' ++ "; break; }")) alts
                        emit "default: {"
                        (d', ss) <- block (gen env d)
                        traverse_ emit ss
                        emit (r ++ " = " ++ d' ++ "; break; }")
                        emit "}"
           pure r
    where
      branch : String -> LowTerm -> C ()
      branch r b
          = do (b', ss) <- block (gen env b)
               traverse_ emit ss
               emit (r ++ " = " ++ b' ++ ";")

      ifs : String -> (LowLit -> String) -> C ()
      ifs r test
          = do traverse_ (\(i, (l, b)) =>
                            do emit ((if i == 0 then "if (" else "} else if (") ++ test l ++ ") {")
                               branch r b) (zip [the Nat 0 .. length alts] alts)
               emit (if null alts then "{" else "} else {")
               branch r d
               emit "}"
  gen env (LCon c t as)
      = do as' <- traverse (gen env) as
           case t of
                TData n _ decl =>
                    if isEnum decl then pure (conTagName t c)
                    else if declNewtype decl then pure (fromMaybe "0" (head' as'))
                    else do v <- fresh "c"
                            let sn = "struct " ++ cName n
                            emit (sn ++ "* " ++ v ++ " = malloc(sizeof(" ++ sn ++ "));")
                            emit (v ++ "->tag = " ++ conTagName t c ++ ";")
                            let tys = map typeOf as
                            traverse_ (\(i, (a, at)) =>
                                         emit (v ++ "->u." ++ cName (conName c) ++
                                               ".f" ++ show i ++ " = " ++
                                               toField (isParamField t c i) at a ++ ";"))
                                      (zip [0 .. length as'] (zip as' tys))
                            pure v
                _ => pure "/* bad constructor */ 0"
  gen env (LFail m)
      = do emit ("fprintf(stderr, \"%s\\n\", " ++ cString m ++ "); abort();")
           pure "0"

  defineFun : Env -> String -> List (String, LowTy) -> LowTerm -> C ()
  defineFun env x caps e@(LLam xs b)
      = do (r, ss) <- block (gen (addVars (xs ++ caps) env) b)
           addFun (funSig x (typeOf e) caps e ++ " {\n" ++
                   indentLines ss ++ "  return " ++ r ++ ";\n}")
  defineFun env x caps e = addFun ("/* " ++ x ++ " is not a function */")

||| Generate a C program: the data type declarations, the lifted functions,
||| and the entry function with the given name.  The entry function takes the
||| free variables of the program, and the parameters of the program if it is
||| a function.
export
toC : String -> LowProg -> String
toC name p
    = let free = progFree p
          (params, body) = case progBody p of
                                LLam xs b => (xs, b)
                                b => ([], b)
          env = MkEnv (params ++ free) []
          used = map cName (map fst free ++ varNames (progBody p))
          res : ((String, List String), CS)
          res = unC (block (gen env body)) (MkCS [] [] 0 used)
          r = fst (fst res)
          ss = snd (fst res)
          st = snd res
          entry = cType (typeOf body) ++ " " ++ name ++ "(" ++
                  joinBy ", " [ cType t ++ " " ++ cName x | (x, t) <- params ++ free ] ++
                  ") {\n" ++ indentLines ss ++
                  "  return " ++ r ++ ";\n}" in
          unlines $
            [ "#include <stdint.h>", "#include <stdlib.h>", "#include <stdio.h>"
            , "#include <string.h>", "#include <math.h>", ""
            , "static inline double void2double(void* p) { double d; memcpy(&d, &p, sizeof d); return d; }"
            , "static inline void* double2void(double d) { void* p = 0; memcpy(&p, &d, sizeof d); return p; }"
            , "" ] ++
            map cDecl (progDecls p) ++ [""] ++
            reverse (csFuns st) ++ [""] ++
            [entry]
