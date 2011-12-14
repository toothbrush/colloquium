{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}

module TestFunctions where

import Unbound.LocallyNameless hiding (Char, Int)
import qualified Language.Haskell.Exts as E
import qualified Language.Haskell.Exts.Pretty as P

import ExampleLanguage

-- capture-avoiding subst:
example_capt0 = parseExp "\\ x -> \\ y -> x"
example_capt1 = parseExp "\\ x -> \\ y -> z"

-- alpha-equivalence
example_eq0  = parseExp "\\ x -> x"
example_eq01 = parseExp "\\ z -> z"

example_eq1  = parseExp "\\ x -> y"
example_eq11 = parseExp "\\ z -> y"

-- parallel reduction tests
example_beta = parseExp "(\\x -> x + 1) y" -- for beta-reduction
example_eta  = parseExp "\\ x -> f x"      -- for eta-conversion

-- parallel reduction function
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
red (Op s e1 e2) = do
                e1' <- red e1
                e2' <- red e2
                return (Op s e1' e2')
red (Lit l) = return (Lit l)
