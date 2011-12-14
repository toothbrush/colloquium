{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}

module ExampleLanguage where

import Unbound.LocallyNameless hiding (Char, Int)
import qualified Language.Haskell.Exts as E
import qualified Language.Haskell.Exts.Pretty as P

------------------------------------------------------------
-- our example AST data type

type N    = Name Exp

data Lit  = Int Prelude.Integer
          | Char Prelude.Char
          | String Prelude.String
          deriving (Show, Eq)

data Exp  = Var N
          | Lit Lit
          | Lam (Bind N Exp)
          | App Exp Exp
          | Op String Exp Exp
          deriving Show

------------------------------------------------------------
-- All we need to be able to use Unbound library!

$(derive [''Lit])

instance Alpha Lit

$(derive [''Exp])

instance Alpha Exp

instance Subst Exp Lit where

instance Subst Exp Exp where
  isvar (Var n) = Just (SubstName n)
  isvar _       = Nothing

instance Eq Exp where
    (==) = aeq

------------------------------------------------------------
-- convert from Haskell src ext AST:

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
