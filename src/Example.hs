{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}

module Example where

import Unbound.LocallyNameless

type N = Name E

data E  = Var N
        | Lit Lit
        | Add E E
        | Let (Bind (N, Embed E) E)
        deriving Show

instance Eq E where
    (==) = aeq

data Lit    = I Integer
            | R Float
            deriving (Show, Eq)

$(derive [''Lit])
instance Alpha Lit

$(derive [''E])

instance Alpha E

instance Subst E Lit where

instance Subst E E where
  isvar (Var n) = Just (SubstName n)
  isvar _       = Nothing

{-


type TyName = Name Type

data Type
  = TyCon String
  | TyVar TyName
  | TyFun Type Type
  | List  Type
  deriving Show

$(derive [''Type])

instance Alpha Type

instance Subst Type Type where
  isvar (TyVar n) = Just (SubstName n)
  isvar _         = Nothing


-}
