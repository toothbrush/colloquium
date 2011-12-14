{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}

module Example where

import Unbound.LocallyNameless hiding (Char, Int)
import qualified Language.Haskell.Exts as E
import qualified Language.Haskell.Exts.Pretty as P

type N = Name Exp

data Exp  = Var N
          | Lit Lit
          | Lam (Bind N Exp)
          | App Exp Exp
          | Op String Exp Exp
          deriving Show

instance Eq Exp where
    (==) = aeq

data Lit    = Int Prelude.Integer
            | Char Prelude.Char
            | String Prelude.String
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
toExp (E.App e1 e2)                       = App (toExp e1) (toExp e2)
toExp (E.Paren e)                         = toExp e
toExp (E.InfixApp e1 op e2)               = Op (toOperator op) (toExp e1) (toExp e2)
toExp e                                   = error $ "toExp: Unsupported: " ++ show e

toOperator (E.QVarOp (E.UnQual (E.Symbol s))) = s

parseExp = toExp . E.fromParseResult . E.parseExp

example0 = parseExp "\\ x -> \\ y -> x"
example1 = parseExp "\\ x -> x"
example2 = parseExp "(\\x -> x + 1) y" -- for beta
example3 = parseExp "\\ x -> y"

red :: Fresh m => Exp -> m Exp
red (Lit l) = return (Lit l)
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
red (Op s e1 e2) = do
                e1' <- red e1
                e2' <- red e2
                return (Op s e1' e2')
