{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}

module Example where

import Unbound.LocallyNameless hiding (Char, Int)
import qualified Language.Haskell.Exts as E

type N = Name Exp

data Exp  = Var N
          | Lit Lit
          | Lam (Bind N Exp)
          | App Exp Exp
          deriving Show

instance Eq Exp where
    (==) = aeq

data Lit    = Int Prelude.Integer
            | Char Prelude.Char
            | String Prelude.String
            | R Prelude.Float
            deriving (Show, Eq)

$(derive [''Lit])
instance Alpha Lit

$(derive [''Exp])

instance Alpha Exp

instance Subst Exp Lit where

instance Subst Exp Exp where
  isvar (Var n) = Just (SubstName n)
  isvar _       = Nothing

toLit (E.Int i)     = Int i
toLit (E.Char c)    = Char c
toLit (E.String s)  = String s
toLit l             = error $ "toLit: Unsupported: " ++ show l

toExp :: E.Exp -> Exp
toExp (E.Lit l)                           = Lit (toLit l)
toExp (E.Var (E.UnQual (E.Ident s)))      = Var (s2n s)
toExp (E.Lambda _ [E.PVar (E.Ident s)] e) = Lam (bind (s2n s) (toExp e))
{-toExp (E.Let (E.BDecls [E.PatBind _ (E.PVar (E.Ident s)) Nothing (E.UnGuardedRhs e1) (E.BDecls [])]) e2)-}
                                          {-= let_ (s2n s) (toExp e1) (toExp e2)-}
{-toExp (E.App ((E.Var (E.UnQual (E.Ident "fix")))) e)-}
                                          {-= fix_ (toExp e)-}
toExp (E.App e1 e2)                       = App (toExp e1) (toExp e2)
toExp (E.Paren e)                         = toExp e
toExp e                                   = error $ "toExp: Unsupported: " ++ show e

parseExp = toExp . E.fromParseResult . E.parseExp

example0 = parseExp "\\ x -> y"
example1 = parseExp "(\\x -> x) y"

captureAvoid :: (Subst b Exp, Fresh m) => Name b -> b -> Exp -> m Exp
captureAvoid n s (Var x) = return (subst n s (Var x))
captureAvoid n s (Lit x) = return (Lit x)
captureAvoid n s (App x y) = undefined
captureAvoid n s (Lam b) = do
                        (x, e) <- unbind b
                        e' <- captureAvoid n s e
                        return (Lam (bind x e'))

red :: Fresh m => Exp -> m Exp
red (Var x) = return (Var x)
red (Lam b) = do
  (x,e) <- unbind b
  e'    <- red e
  case e' of -- eta-rule
      App e'' (Var y) | x == y && not (x `elem` fv e'') -> return e''
      _                -> return (Lam (bind x e'))
red (App e1 e2) = do
    e1' <- red e1
    case e1' of
        Lam b -> do -- beta-rule
            (x, e') <- unbind b
            e2' <- red e2
            return (subst x e2' e')
        _ -> do
            e2' <- red e2
            return (App e1' e2')
