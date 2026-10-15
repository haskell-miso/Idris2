||| A staged interpreter for the simply typed lambda calculus (Kovács,
||| "Staged Compilation with Two-Level Type Theory", section 2.2): embedded
||| terms are interpreted into object level code, with no interpretation
||| overhead left at run time.
module STLC

import Language.Staged

data Ty = Base | Fun Ty Ty

data Con = Empty | Ext Con Ty

data Var : Con -> Ty -> Type where
  VZ : Var (Ext g a) a
  VS : Var g a -> Var (Ext g b) a

data Tm : Con -> Ty -> Type where
  V : Var g a -> Tm g a
  Lam : Tm (Ext g a) b -> Tm g (Fun a b)
  App : Tm g (Fun a b) -> Tm g a -> Tm g b

-- Types are interpreted as object level types, at compile time
EvalTy : Ty -> Code Type
EvalTy Base = Int
EvalTy (Fun a b) = EvalTy a -> EvalTy b

-- Contexts are static lists of object level variables (partially static data)
EvalCon : Con -> Type
EvalCon Empty = ()
EvalCon (Ext g a) = (EvalCon g, Code (EvalTy a))

EvalVar : Var g a -> EvalCon g -> Code (EvalTy a)
EvalVar VZ (env, v) = v
EvalVar (VS x) (env, v) = EvalVar x env

EvalTm : Tm g a -> EvalCon g -> Code (EvalTy a)
EvalTm (V x) env = EvalVar x env
EvalTm (Lam t) env = \v => EvalTm t (env, v)
EvalTm (App t u) env = EvalTm t env (EvalTm u env)

-- \f, x => f (f x)
twice : Tm Empty (Fun (Fun Base Base) (Fun Base Base))
twice = Lam (Lam (App (V (VS VZ)) (App (V (VS VZ)) (V VZ))))

-- staged to \f, x => f (f x)
twiceVal : EvalTy (Fun (Fun Base Base) (Fun Base Base))
twiceVal = EvalTm twice ()

main : IO ()
main = printLn (twiceVal (\n => n * 10) 3)
