||| A code generator from low code to JavaScript, as an example of a user
||| written backend for Language.Staged.Low.  A value of a data type whose
||| constructors have no fields (e.g. Bool) is its tag (a number), other data
||| values are arrays [tag, field, ...], a newtype is its field.  Int and
||| Double are numbers (so an Int is exact up to 2^53 only), Integer is
||| BigInt, Char is its code point and String is a string.  Local functions
||| are JavaScript functions, a case is a switch.
|||
||| The entry point is toJS; the generated program defines a function with
||| the given name that takes the parameters of the program (if it is a
||| function) and its free variables, and returns the result.
module Language.Staged.Low.JS

import Data.List
import Data.Maybe
import Data.String
import Language.Staged.Low

%default covering

-- Statements are collected (in reverse), with a counter for fresh names and
-- the names used by the program
record JS where
  constructor MkJS
  jsStmts : List String
  jsUniq : Nat
  jsUsed : List String

record J a where
  constructor MkJ
  unJ : JS -> (a, JS)

Functor J where
  map f (MkJ g) = MkJ $ \s => let (a, s') = g s in (f a, s')

Applicative J where
  pure a = MkJ $ \s => (a, s)
  MkJ f <*> MkJ a = MkJ $ \s => let (g, s') = f s
                                    (b, s'') = a s' in (g b, s'')

Monad J where
  MkJ g >>= f = MkJ $ \s => let (a, s') = g s in unJ (f a) s'

emit : String -> J ()
emit l = MkJ $ \s => ((), { jsStmts $= (l ::) } s)

-- Run a statement block, and return its statements
block : J a -> J (a, List String)
block act = MkJ $ \s =>
  let (a, s') = unJ act ({ jsStmts := [] } s) in
      ((a, reverse (jsStmts s')), { jsStmts := jsStmts s } s')

||| A JavaScript identifier for a name of the program
export
jsName : String -> String
jsName = concatMap esc . unpack . baseName
  where
    esc : Char -> String
    esc c = if (isAlphaNum c && ord c < 128) || c == '_' then singleton c
            else if c == '\'' then "_q"
            else "_" ++ show (ord c) ++ "_"

fresh : String -> J String
fresh b = MkJ $ \s =>
  let n = pick (jsUsed s) (jsUniq s) (length (jsUsed s) + 1) in
      (b ++ "_" ++ show n, { jsUniq := S n } s)
  where
    pick : List String -> Nat -> Nat -> Nat
    pick used i Z = i
    pick used i (S k) = if (b ++ "_" ++ show i) `elem` used then pick used (S i) k else i

isEnumTy : LowTy -> Bool
isEnumTy (TData _ _ d) = not (declNewtype d) && all (null . conDeclFields) (declCons d)
isEnumTy _ = False

jsString : String -> String
jsString s = "\"" ++ concatMap esc (unpack s) ++ "\""
  where
    hex4 : Int -> String
    hex4 n = pack (map digit [n `div` 4096, (n `div` 256) `mod` 16, (n `div` 16) `mod` 16, n `mod` 16])
      where
        digit : Int -> Char
        digit d = if d < 10 then chr (ord '0' + d) else chr (ord 'a' + d - 10)

    esc : Char -> String
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc c = if ord c < 32 || (ord c > 126 && ord c < 65536)
               then "\\u" ++ hex4 (ord c)
               else singleton c

jsLit : LowLit -> String
jsLit (LitInt i) = show i
jsLit (LitInteger i) = show i ++ "n"
jsLit (LitDouble d) = show d
jsLit (LitChar c) = show (ord c)
jsLit (LitString s) = jsString s
jsLit (LitFixed _ i) = show i

-- prim__add_Int is ("add", "Int")
primParts : String -> Maybe (String, String)
primParts p
    = if isPrefixOf "prim__" p
         then case break (== '_') (unpack (substr 6 (length p) p)) of
                   (op, '_' :: ty) => Just (pack op, pack ty)
                   _ => Nothing
         else Nothing

-- The primitives that low code can use
prim : String -> List String -> String
prim p as
    = case (primParts p, as) of
           (Just ("div", ty), [a, b]) =>
               if ty == "Double" || ty == "Integer" then bin "/" a b
                  else "Math.trunc(" ++ a ++ " / " ++ b ++ ")"
           (Just (op, _), [a, b]) =>
               case lookup op arith of
                    Just o => bin o a b
                    Nothing => case lookup op compare of
                                    Just o => "(" ++ a ++ " " ++ o ++ " " ++ b ++ " ? 1 : 0)"   -- as Idris: 0 or 1
                                    Nothing => unknown
           (Just ("neg", _), [a]) => "(-" ++ a ++ ")"
           (Just ("cast", tys), [a]) => cast tys a
           _ => case (p, as) of
                     ("prim__doubleExp", [a]) => "Math.exp(" ++ a ++ ")"
                     ("prim__doubleLog", [a]) => "Math.log(" ++ a ++ ")"
                     ("prim__doubleSin", [a]) => "Math.sin(" ++ a ++ ")"
                     ("prim__doubleCos", [a]) => "Math.cos(" ++ a ++ ")"
                     ("prim__doubleSqrt", [a]) => "Math.sqrt(" ++ a ++ ")"
                     ("prim__doubleFloor", [a]) => "Math.floor(" ++ a ++ ")"
                     ("prim__doubleCeiling", [a]) => "Math.ceil(" ++ a ++ ")"
                     _ => unknown
  where
    bin : String -> String -> String -> String
    bin o a b = "(" ++ a ++ " " ++ o ++ " " ++ b ++ ")"

    arith : List (String, String)
    arith = [ ("add", "+"), ("sub", "-"), ("mul", "*"), ("mod", "%")
            , ("shl", "<<"), ("shr", ">>"), ("and", "&"), ("or", "|"), ("xor", "^") ]

    compare : List (String, String)
    compare = [ ("lt", "<"), ("lte", "<="), ("eq", "==="), ("gte", ">="), ("gt", ">") ]

    unknown : String
    unknown = "/* unknown primitive " ++ p ++ " */ " ++ jsName p ++ "(" ++ joinBy ", " as ++ ")"

    cast : String -> String -> String
    cast tys a
        = if isPrefixOf "Integer" tys && tys /= "Integer" then "Number(" ++ a ++ ")"
          else if isSuffixOf "Integer" tys && tys /= "Integer" then "BigInt(" ++ a ++ ")"
          else if tys == "DoubleInt" then "Math.trunc(" ++ a ++ ")"
          else a

mutual
  -- The value of a term, after emitting the statements that compute it
  gen : LowTerm -> J String
  gen (LVar x _) = pure (jsName x)
  gen (LLit l _) = pure (jsLit l)
  gen (LPrim p _) = pure ("/* primitive " ++ p ++ " */")
  gen (LForeign _ c _) = pure c
  gen (LApp f as)
      = do as' <- traverse gen as
           case f of
                LPrim p _ => pure (prim p as')
                _ => do f' <- gen f
                        pure (f' ++ "(" ++ joinBy ", " as' ++ ")")
  gen (LLam xs b)
      = do f <- fresh "f"
           defFun f xs b
           pure f
  gen (LLet x _ (LLam xs e) b)
      = do defFun (jsName x) xs e
           gen b
  gen (LLet x _ e b)
      = do e' <- gen e
           emit ("const " ++ jsName x ++ " = " ++ e' ++ ";")
           gen b
  gen (LLetRec bs b)
      = do -- function declarations are hoisted, so they can call each other
           traverse_ (\(x, _, e) =>
                        case e of
                             LLam xs e' => defFun (jsName x) xs e'
                             _ => do e' <- gen e
                                     emit ("const " ++ jsName x ++ " = " ++ e' ++ ";")) bs
           gen b
  gen (LCase s cons alts d)
      = do s' <- gen s
           r <- fresh "r"
           emit ("let " ++ r ++ ";")
           let st = typeOf s
           case (st, alts) of
                (TData _ _ decl, [(_, [(x, _)], b)]) =>
                    if declNewtype decl
                       then do emit ("const " ++ jsName x ++ " = " ++ s' ++ ";")
                               b' <- gen b
                               emit (r ++ " = " ++ b' ++ ";")
                       else switch st s' r
                _ => switch st s' r
           pure r
    where
      alt : String -> String -> (LowCon, List (String, LowTy), LowTerm) -> J ()
      alt s' r (c, xs, b)
          = do emit ("case " ++ show (conTag c) ++ ": {")
               traverse_ (\(i, (x, _)) =>
                            emit ("const " ++ jsName x ++ " = " ++ s' ++ "[" ++ show i ++ "];"))
                         (zip [the Nat 1 .. length xs] xs)
               (b', ss) <- block (gen b)
               traverse_ emit ss
               emit (r ++ " = " ++ b' ++ "; break; }")

      switch : LowTy -> String -> String -> J ()
      switch st s' r
          = do emit ("switch (" ++ (if isEnumTy st then s' else s' ++ "[0]") ++ ") {")
               traverse_ (alt s' r) alts
               case d of
                    Just e => when (length alts < length cons) $
                                do emit "default: {"
                                   (e', ss) <- block (gen e)
                                   traverse_ emit ss
                                   emit (r ++ " = " ++ e' ++ "; break; }")
                    Nothing => pure ()
               emit "}"
  gen (LCaseLit s alts d)
      = do s' <- gen s
           r <- fresh "r"
           emit ("let " ++ r ++ ";")
           emit ("switch (" ++ s' ++ ") {")
           traverse_ (\(l, b) =>
                        do emit ("case " ++ jsLit l ++ ": {")
                           (b', ss) <- block (gen b)
                           traverse_ emit ss
                           emit (r ++ " = " ++ b' ++ "; break; }")) alts
           emit "default: {"
           (d', ss) <- block (gen d)
           traverse_ emit ss
           emit (r ++ " = " ++ d' ++ "; break; }")
           emit "}"
           pure r
  gen (LCon c t as)
      = do as' <- traverse gen as
           if conNewtype c
              then pure (fromMaybe "undefined" (head' as'))
              else if isEnumTy t
              then pure (show (conTag c))
              else pure ("[" ++ joinBy ", " (show (conTag c) :: as') ++ "]")
  gen (LFail m) = pure ("(() => { throw new Error(" ++ jsString m ++ "); })()")

  -- A function declaration
  defFun : String -> List (String, LowTy) -> LowTerm -> J ()
  defFun f xs b
      = do (r, ss) <- block (gen b)
           emit ("function " ++ f ++ "(" ++ joinBy ", " (map (jsName . fst) xs) ++ ") {")
           traverse_ (emit . ("  " ++)) ss
           emit ("  return " ++ r ++ ";")
           emit "}"

||| Generate a JavaScript function with the given name
export
toJS : String -> LowProg -> String
toJS name p
    = let (params, body) = case progBody p of
                                LLam xs b => (xs, b)
                                b => ([], b)
          args = map (jsName . fst) (params ++ progFree p)
          used = map jsName (map fst (progFree p) ++ varNames (progBody p))
          res : ((String, List String), JS)
          res = unJ (block (gen body)) (MkJS [] 0 used)
          r = fst (fst res)
          ss = snd (fst res) in
          unlines $
            [ "// " ++ show d | d <- progDecls p ] ++
            [ "function " ++ name ++ "(" ++ joinBy ", " args ++ ") {" ] ++
            map ("  " ++) ss ++
            [ "  return " ++ r ++ ";", "}" ]
