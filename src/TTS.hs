{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

--------------------------------------------------------------------------------

module Main where

--------------------------------------------------------------------------------

import qualified Prelude
import Prelude hiding (abs, print, putStr, putStrLn)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (maximumBy, sortBy, permutations)
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import Control.Arrow (first, second)
import Control.Monad (liftM, liftM2, ap, unless, foldM_, msum)
import Data.Function (fix)

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Error (ErrorT, runErrorT)

import Control.Monad.Logic (LogicT, observeAllT)

import Unbound.LocallyNameless hiding (apply, compose, union, GT, Int, Char)

import qualified Language.Haskell.Exts as E

--------------------------------------------------------------------------------

(<$>) :: (Monad m) => (a -> b) -> m a -> m b
(<$>) = liftM

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap

infixl 4 <$>, <*>

failUnlessNull ls msg = unless (null ls) $ fail $ msg ++ ": " ++ show ls

print s = liftIO (Prelude.print s)
putStr s = liftIO (Prelude.putStr s)
putStrLn s = liftIO (Prelude.putStrLn s)

prettyOneLine =
  E.prettyPrintStyleMode (E.style { E.mode = E.OneLineMode }) E.defaultMode

--------------------------------------------------------------------------------

union :: (Ord a) => [(a, b)] -> [(a, b)] -> [(a, b)]
union s1 s2 = M.toList $ M.fromList s1 `M.union` M.fromList s2

delete :: (Eq a) => a -> [(a, b)] -> [(a, b)]
delete k = filter (\(x,_) -> k /= x)

collect :: (Eq a) => a -> [(a, b)] -> [(a, b)]
collect k = filter (\(x,_) -> k == x)

mapCollect :: (Eq a) => a -> (b -> c) -> [(a, b)] -> [c]
mapCollect v c = map (c . snd) . collect v

intersection :: (Ord a) => [(a, b)] -> [(a, c)] -> [(a, (b, c))]
intersection x y = M.toList $ M.intersectionWith (,) (M.fromList x) (M.fromList y)

dom :: [(a, b)] -> [a]
dom = map fst

ran :: [(a, b)] -> [b]
ran = map snd

isSubsetOf :: (Ord a) => [a] -> [a] -> Bool
isSubsetOf x y = S.fromList x `S.isSubsetOf` S.fromList y

(\\) :: (Ord a) => [a] -> [a] -> [a]
(\\) x y = S.toList $ S.fromList x S.\\ S.fromList y

duplicates :: (Ord a) => [a] -> [a]
duplicates l = go l S.empty
  where
    go [] _           = []
    go (x:xs) us
      | x `S.member` us = x : go xs us
      | otherwise       = go xs (S.insert x us)

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

instance Eq Type where
  (==) = aeq

--------------------------------------------------------------------------------

apply :: (Subst b a) => [(Name b, b)] -> a -> a
apply = substs

apply2 :: (Subst b a, Subst c a) => [(Name b, b)] -> [(Name c, c)] -> a -> a
apply2 sb1 sb2 = apply sb1 . apply sb2

compose :: (Subst b b) => [(Name b, b)] -> [(Name b, b)] -> [(Name b, b)]
compose s1 s2 = apply s1 s2 `union` s1

--------------------------------------------------------------------------------

mgu (TyCon s1) (TyCon s2) | s1 == s2 = return []
mgu (TyVar v1) (TyVar v2) | v1 == v2 = return []

mgu (TyVar v) t = bindTyVar v t
mgu t (TyVar v) = bindTyVar v t

mgu (TyFun t1 u1) (TyFun t2 u2) = do
  sb1 <- mgu t1 t2
  sb2 <- mgu (apply sb1 u1) (apply sb1 u2)
  return (sb2 `compose` sb1)

mgu (List t1) (List t2) = do
  sb <- mgu t1 t2
  return sb

mgu t1 t2 =
  fail $ "No mgu of \"" ++ show t1 ++ "\" and \"" ++ show t2 ++ "\""

bindTyVar v t
  | v `S.member` fv t =
    fail $ "Occurs check: \"" ++ show v ++ "\" in \"" ++ show t ++ "\""
  | otherwise = return [(v, t)]

--------------------------------------------------------------------------------

data Scheme =
  Forall (Bind [TyName] Type)
  deriving Show

$(derive [''Scheme])

instance Alpha Scheme

instance Subst Type Scheme where

--------------------------------------------------------------------------------

forall vs t = Forall (bind vs t)

unbindForall b = do
  (vs, t) <- unbind b
  return (vs, t)

instance Eq Scheme where
  (==) = aeq

--------------------------------------------------------------------------------

class FreshVar a where
  freshTyVar :: (Fresh m) => a -> m Type

instance FreshVar (Name a) where
  freshTyVar n = return $ TyVar (translate n)

instance FreshVar String where
  freshTyVar s = fresh (s2n s :: TyName) >>= freshTyVar

--------------------------------------------------------------------------------

inst :: (Fresh m) => Scheme -> m Type
inst (Forall b) =  unbindForall b >>= \(_, t) -> return t

gen :: (Alpha a) => a -> Type -> Scheme
gen env ty = forall (S.toList $ fv ty S.\\ fv env) ty

gen' :: Type -> Scheme
gen' = gen ([] :: [Int])

--------------------------------------------------------------------------------

data Constraint
  = TyEq Type Type
  | ExplInst Type Scheme
  | ImplInst [Type] Type Type
  deriving Show

$(derive [''Constraint])

instance Alpha Constraint

instance Subst Type Constraint where

--------------------------------------------------------------------------------

class Active c where
  active :: (Rep a) => c -> S.Set (Name a)

instance Active Constraint where
  active (TyEq t1 t2) = fv t1 `S.union` fv t2
  active (ExplInst t sc) = fv t `S.union` fv sc
  active (ImplInst monos t1 t2) = fv t1 `S.union` (fv monos `S.intersection` fv t2)

instance Active [Constraint] where
  active = S.unions . map active

--------------------------------------------------------------------------------

orderable :: [Type] -> [Constraint] -> Type -> Bool
orderable monos csts ty =
  (fv ty `S.intersection` active csts :: S.Set TyName) `S.isSubsetOf` fv monos

solve [] = return ([], [])
solve (c : cs) = case c of
  TyEq t1 t2 -> do
    sb1 <- mgu t1 t2
    (sb2, cs') <- solve (apply sb1 cs)
    return (sb2 `compose` sb1, cs')
  ExplInst t1 sc2 -> do
    t2 <- inst sc2
    solve (TyEq t1 t2 : cs)
  ImplInst monos t1 t2 | orderable monos (c : cs) t2 ->
    solve (ExplInst t1 (gen monos t2) : cs)
  ImplInst monos t1 t2 | otherwise -> do
    (sb, cs') <- solve cs
    return (sb, c : cs')

--------------------------------------------------------------------------------

data Lit
  = Int Integer
  | Char Char
  | String String
  deriving (Show, Eq)

$(derive [''Lit])

instance Alpha Lit

--------------------------------------------------------------------------------

type EName = Name Exp

data Ann = Ann
  { weight_      :: !Int
  , assumptions_ :: [(EName, Type)]
  , constraints_ :: [Constraint]
  , typeOf_      :: Type
  }
  deriving Show

data Exp
  = Lit Lit                           (Maybe Ann)
  | Var EName                         (Maybe Ann)
  | Abs (Bind EName Exp)              (Maybe Ann)
  | App Exp Exp                       (Maybe Ann)
  | Let (Bind (EName, Embed Exp) Exp) (Maybe Ann)
  | Fix Exp                           (Maybe Ann)
  deriving Show

$(derive [''Ann])
$(derive [''Exp])

instance Alpha Ann
instance Alpha Exp

instance Subst Exp Ann where
instance Subst Exp Exp where
  isvar (Var n _) = Just (SubstName n)
  isvar _         = Nothing
instance Subst Exp Lit where
instance Subst Exp Type where
instance Subst Exp Scheme where
instance Subst Exp Constraint where
instance Subst Type Lit where
instance Subst Type Ann where
instance Subst Type Exp where

--------------------------------------------------------------------------------

abs' v e        = Abs (bind v e)
let_' v e1 e2   = Let (bind (v, embed e1) e2)

unbindAbs       = unbind
unbindLet b     = do ((v, e1), e2) <- unbind b
                     return (v, unembed e1, e2)

lit l           = Lit l Nothing
var v           = Var v Nothing
abs v e         = abs' v e Nothing
let_ v e1 e2    = let_' v e1 e2 Nothing
app e1 e2       = App e1 e2 Nothing
fix_ e          = Fix e Nothing

resetExp (Lit l _) = return $ lit l
resetExp (Var v _) = return $ var v
resetExp (Abs b _) = do
  (v, e) <- unbindAbs b
  e' <- resetExp e
  return $ abs v e'
resetExp (App e1 e2 _) = do
  e1' <- resetExp e1
  e2' <- resetExp e2
  return $ app e1' e2'
resetExp (Let b _) = do
  (v, e1, e2) <- unbindLet b
  e1' <- resetExp e1
  e2' <- resetExp e2
  return $ let_ v e1' e2'
resetExp (Fix e _) = do
  e' <- resetExp e
  return $ fix_ e'

instance Eq Exp where
  e1 == e2 = runFreshM $ liftM2 aeq (resetExp e1) (resetExp e2)

--------------------------------------------------------------------------------

data Env m = Env (m [(EName, Scheme)]) (Lit -> m Type)

lookupVar v (Env vars _   ) = lookup v <$> vars
deleteVar v (Env vars lits) = Env (delete v <$> vars) lits
typeOfLit l (Env _    lits) = lits l
applyEnv sb (Env vars lits) = Env (apply sb <$> vars) lits

--------------------------------------------------------------------------------

infer' env monos e = do
  e' <- fix prop' env monos e
  return (assumptions e', constraints e', typeOf e')

--------------------------------------------------------------------------------

infer env expr = do
  (asms, csts, ty) <- infer' env [] expr
  failUnlessNull asms "infer: Unbound variables"
  failUnlessNull csts "infer: Unsolvable constraints"
  return ty

--------------------------------------------------------------------------------

ann (Lit _   a) = a
ann (Var _   a) = a
ann (Abs _   a) = a
ann (App _ _ a) = a
ann (Let _   a) = a
ann (Fix _   a) = a

upd f (Lit l   a) = Lit l (f <$> a)
upd f (Var v   a) = Var v (f <$> a)
upd f (Abs b   a) = Abs b (f <$> a)
upd f (App x y a) = App x y (f <$> a)
upd f (Let b   a) = Let b (f <$> a)
upd f (Fix e   a) = Fix e (f <$> a)

weight      = weight_      . fromJust . ann
assumptions = assumptions_ . fromJust . ann
constraints = constraints_ . fromJust . ann
typeOf      = typeOf_      . fromJust . ann

addWeight w' = upd (\(Ann w a c t) -> Ann (w + w') a c t)

--------------------------------------------------------------------------------

resolve e wt asms [] ty =
  return $ e $ Just $ Ann wt asms [] ty
resolve e wt asms csts ty = do
  (sb, csts') <- solve csts
  return $ e $ Just $ Ann wt (apply sb asms) csts' (apply sb ty)

--------------------------------------------------------------------------------

prop' rec env monos expr = case expr of

  Lit l Nothing -> do
    t <- typeOfLit l env
    resolve (Lit l) 0 [] [] t

  Var v Nothing -> do
    mv_sc <- lookupVar v env
    case mv_sc of
      Nothing -> do
        v_ty <- freshTyVar v
        resolve (Var v) 0 [(v, v_ty)] [] v_ty
      Just v_sc -> do
        v_ty <- inst v_sc
        resolve (Var v) 0 [] [] v_ty

  Abs b Nothing -> do
    (v, e) <- unbindAbs b
    v_ty <- freshTyVar v
    e' <- rec (deleteVar v env) (v_ty : monos) e
    let v_csts = mapCollect v (TyEq v_ty) (assumptions e')
    resolve (abs' v e')
            (weight e')
            (delete v (assumptions e'))
            (v_csts ++ constraints e')
            (TyFun v_ty (typeOf e'))

  App e1 e2 Nothing -> do
    e1' <- rec env monos e1
    e2' <- rec env monos e2
    r_ty <- freshTyVar "a"
    resolve (App e1' e2')
            (weight e1' + weight e2')
            (assumptions e1' ++ assumptions e2')
            (constraints e1' ++ constraints e2' ++ [TyEq (typeOf e1') (TyFun (typeOf e2') r_ty)])
            r_ty

  Let b Nothing -> do
    (v, e1, e2) <- unbindLet b
    e1' <- rec env monos e1
    e2' <- rec (deleteVar v env) monos e2
    let v_csts = mapCollect v (\v_ty -> ImplInst monos v_ty (typeOf e1')) (assumptions e2')
    resolve (let_' v e1' e2')
            (weight e1' + weight e2')
            (assumptions e1' ++ delete v (assumptions e2'))
            (constraints e1' ++ v_csts ++ constraints e2')
            (typeOf e2')

  Fix e Nothing -> do
    e' <- rec env monos e
    r_ty <- freshTyVar "r"
    resolve (Fix e')
            (weight e')
            (assumptions e')
            (constraints e' ++ [TyEq (typeOf e') (TyFun r_ty r_ty)])
            r_ty

--------------------------------------------------------------------------------

prop tf env e = do
  e' <- fix (\r en m ex -> prop' r en m ex >>= tf en m) env [] e
  failUnlessNull (dom $ assumptions e') "prop: Unbound variables"
  failUnlessNull (constraints e') "prop: Unsolvable constraints"
  return e'

--------------------------------------------------------------------------------

data RPat
  = RLit Lit
  | RVar EName
  | RMVar EName
  | RApp RPat RPat
  | RTag RPat Integer
  deriving Show

--------------------------------------------------------------------------------

inferRPat' env pat = case pat of

  RLit l -> do
    t <- typeOfLit l env
    return ([], [], t)

  RVar v -> do
    mv_sc <- lookupVar v env
    case mv_sc of
      Just v_sc -> do
        v_ty <- inst v_sc
        return ([], [], v_ty)
      Nothing -> fail $ "Var '" ++ show v ++ "' not found in environment"

  RMVar v -> do
    v_ty <- freshTyVar v
    return ([(v, v_ty)], [], v_ty)

  RApp p1 p2 -> do
    (p1_asms, p1_sb, p1_ty) <- inferRPat' env p1
    (p2_asms, p2_sb, p2_ty) <- inferRPat' (applyEnv p1_sb env) p2
    r_ty <- freshTyVar "a"
    sb <- mgu (apply p2_sb p1_ty) (TyFun p2_ty r_ty)
    return (apply sb (apply p2_sb p1_asms ++ apply p1_sb p2_asms), sb `compose` p2_sb `compose` p1_sb, apply sb r_ty)

  RTag p n -> do
    (p_asms, p_sb, p_ty) <- inferRPat' env p
    i_ty <- freshTyVar "g"
    __ <- mgu i_ty p_ty
    return (p_asms, p_sb, p_ty)

--------------------------------------------------------------------------------

inferRPat env pat = do
    (asms, _, ty) <- inferRPat' env pat
    let dup_mvars = duplicates (dom asms)
    failUnlessNull dup_mvars "inferRPat: Non-linear pattern. Duplicate variables"
    return (asms, ty)

--------------------------------------------------------------------------------

data Rule
  = Rule Int RPat RPat
  deriving Show

--------------------------------------------------------------------------------

inferRule env (Rule _ p1 p2) = do
  (p1_asms, ty1) <- inferRPat env p1
  (p2_asms, ty2) <- inferRPat env p2
  let unscoped_mvars = dom p2_asms \\ dom p1_asms
      mvar_ty_changes = p1_asms `intersection` p2_asms
  failUnlessNull unscoped_mvars "inferRule: Metavariables not in scope"
  return (mvar_ty_changes, ty1, ty2)

--------------------------------------------------------------------------------

rmatch (RLit l1)     (Lit l2 _) | l1 == l2 = return []
rmatch (RVar v1)     (Var v2 _) | v1 == v2 = return []
rmatch (RMVar mv)    e                     = return [(mv, e)]
rmatch (RApp p1 p2)  (App e1 e2 _)         = do s1 <- rmatch p1 e1
                                                s2 <- rmatch p2 e2
                                                return $ s1 ++ s2
rmatch p             e                     =
  fail $ "rmatch: No match for pattern '" ++ show p ++ "' at term '" ++ show e ++ "'"

rapply env sb = go
  where
    go pat = case pat of
      RLit l -> do
        t <- typeOfLit l env
        resolve (Lit l) 0 [] [] t

      RVar v -> do
        mv_sc <- lookupVar v env
        case mv_sc of
          Just v_sc -> do
            v_ty <- inst v_sc
            resolve (Var v) 0 [] [] v_ty
          Nothing -> error $ "rapply: Unbound variable: " ++ show v

      RMVar mv -> do
        return $ apply sb (var mv)

      RApp p1 p2 -> do
        e1 <- go p1
        e2 <- go p2
        r_ty <- freshTyVar "a"
        resolve (App e1 e2)
                (weight e1 + weight e2)
                (assumptions e1 ++ assumptions e2)
                (constraints e1 ++ constraints e2 ++ [TyEq (typeOf e1) (TyFun (typeOf e2) r_ty)])
                r_ty

      RTag p n -> do
        e <- go p
        i_ty <- freshTyVar "g"
        _ <- mgu i_ty (typeOf e)
        return $ e

rewrite env e r@(Rule w p1 p2) = do
  sb <- rmatch p1 e
  addWeight w <$> rapply env sb p2

--------------------------------------------------------------------------------

instance (Fresh m) => Fresh (LogicT m) where
  fresh = lift . fresh

revOrd o = case o of { LT -> GT ; GT -> LT ; e -> e }
comparingRev f x y = revOrd $ comparing f x y

selectNonnegWeights = filter ((>= 0) . weight)
sortByWeight = sortBy (comparingRev weight) . selectNonnegWeights
maxByWeight = maximumBy (comparing weight) . selectNonnegWeights

--------------------------------------------------------------------------------

transform rules env _monos e = msum . map (rewrite env e) $ rules

transformWith' rules env e = prop (transform rules) env e

transformWith rules env e = runFreshMT $ do
  e' <- maxByWeight <$> observeAllT (transformWith' rules env e)
  return (e', typeOf e')

--------------------------------------------------------------------------------

toLit (E.Int i)     = Int i
toLit (E.Char c)    = Char c
toLit (E.String s)  = String s
toLit l             = error $ "toLit: Unsupported: " ++ show l

fromLit (Int i)     = E.Int i
fromLit (Char c)    = E.Char c
fromLit (String s)  = E.String s

--------------------------------------------------------------------------------

-- Note that this syntax does not support 'fix' in a higher-order way
toExp :: E.Exp -> Exp
toExp (E.Lit l)                           = lit (toLit l)
toExp (E.Var (E.UnQual (E.Ident s)))      = var (s2n s)
toExp (E.Lambda _ [E.PVar (E.Ident s)] e) = abs (s2n s) (toExp e)
toExp (E.Let (E.BDecls [E.PatBind _ (E.PVar (E.Ident s)) Nothing (E.UnGuardedRhs e1) (E.BDecls [])]) e2)
                                          = let_ (s2n s) (toExp e1) (toExp e2)
toExp (E.App ((E.Var (E.UnQual (E.Ident "fix")))) e)
                                          = fix_ (toExp e)
toExp (E.App e1 e2)                       = app (toExp e1) (toExp e2)
toExp (E.Paren e)                         = toExp e
toExp e                                   = error $ "toExp: Unsupported: " ++ show e

parseExp = toExp . E.fromParseResult . E.parseExp

--------------------------------------------------------------------------------

noSrcLoc = E.SrcLoc "" 0 0

fromExp :: (Fresh m) => Exp -> m E.Exp
fromExp (Lit l _)          = return $ E.Lit (fromLit l)
fromExp (Var n _)          = return $ E.Var (E.UnQual (E.Ident (show n)))
fromExp (Abs b _)          = do (n, e) <- unbindAbs b
                                e' <- fromExp e
                                return $ E.Lambda noSrcLoc [E.PVar (E.Ident (show n))] e'
fromExp (Let b _)          = do (n, e1, e2) <- unbindLet b
                                e1' <- fromExp e1
                                e2' <- fromExp e2
                                return $ E.Let (E.BDecls [E.PatBind noSrcLoc (E.PVar (E.Ident (show n))) Nothing (E.UnGuardedRhs e1') (E.BDecls [])]) e2'
fromExp (Fix e _)          = do e' <- fromExp e
                                return $ E.App ((E.Var (E.UnQual (E.Ident "fix")))) e'
fromExp (App e1 e2 _)      = do e1' <- fromExp e1
                                e2' <- fromExp e2
                                return $ E.App e1' e2'

prettyExp = prettyOneLine . runFreshM . fromExp

--------------------------------------------------------------------------------

toType (E.TyCon (E.UnQual (E.Ident s))) = TyCon <$> return s
toType (E.TyVar (E.Ident s))            = TyVar <$> return (s2n s)
toType (E.TyFun t1 t2)                  = TyFun <$> toType t1 <*> toType t2
toType (E.TyList t)                     = List <$> toType t
toType (E.TyParen t)                    = toType t

parseType = toType . E.fromParseResult . E.parseType

--------------------------------------------------------------------------------

fromType :: Type -> E.Type
fromType (TyCon s)     = E.TyCon (E.UnQual (E.Ident s))
fromType (TyVar n)     = E.TyVar (E.Ident (show n))
fromType (TyFun t1 t2) = E.TyFun (fromType t1) (fromType t2)
fromType (List  t)     = E.TyList (fromType t)

prettyType = prettyOneLine . fromType

--------------------------------------------------------------------------------

toTyName :: E.TyVarBind -> TyName
toTyName (E.UnkindedVar (E.Ident s)) = s2n s

toScheme (E.TyForall (Just vs) [] t) = do t' <- toType t
                                          return $ forall (map toTyName vs) t'
toScheme t                           = error $ "toScheme: Unsupported: " ++ show t

parseScheme = toScheme . E.fromParseResult . E.parseTypeWithMode mode
  where
    mode = E.defaultParseMode { E.extensions = [E.ExplicitForall] }

--------------------------------------------------------------------------------

fromTyName :: TyName -> E.TyVarBind
fromTyName n = E.UnkindedVar (E.Ident (show n))

fromScheme :: (Fresh m) => Scheme -> m E.Type
fromScheme (Forall b) = do
  (vs, t) <- unbindForall b
  return $ E.TyForall (Just (map fromTyName vs)) [] (fromType t)

prettyScheme = prettyOneLine . runFreshM . fromScheme

--------------------------------------------------------------------------------

printVarScheme (v, s) = do
  putStr (show v)
  putStr " : "
  putStrLn (prettyScheme s)

printEnv (Env vs _) = runFreshMT $ vs >>= mapM_ printVarScheme

--------------------------------------------------------------------------------

toRPat :: E.Exp -> RPat
toRPat (E.Lit l)                        = RLit (toLit l)
toRPat (E.Var (E.UnQual (E.Ident s)))   = RVar (s2n s)
toRPat (E.Con (E.UnQual (E.Ident s)))   = RMVar (s2n s)
toRPat (E.App p1 p2)                    = RApp (toRPat p1) (toRPat p2)
toRPat (E.Paren p)                      = toRPat p
toRPat (E.InfixApp p (E.QVarOp (E.UnQual (E.Ident "as"))) (E.Lit (E.Int n)))
                                        = RTag (toRPat p) n
toRPat p                                = error $ "toRPat: Unsupported: " ++ show p

parseRPat = toRPat . E.fromParseResult . E.parseExp

--------------------------------------------------------------------------------

fromRPat :: RPat -> E.Exp
fromRPat (RLit l)               = E.Lit (fromLit l)
fromRPat (RVar n)               = E.Var (E.UnQual (E.Ident (show n)))
fromRPat (RMVar n)              = E.Con (E.UnQual (E.Ident (show n)))
fromRPat (RApp p1 p2)           = E.App (fromRPat p1) (fromRPat p2)
fromRPat (RTag p n)             = E.InfixApp (fromRPat p) (E.QVarOp (E.UnQual (E.Ident "as"))) (E.Lit (E.Int n))

prettyRPat = prettyOneLine . fromRPat

--------------------------------------------------------------------------------

toRule :: Int -> E.Exp -> Rule
toRule wt (E.InfixApp p1 (E.QVarOp (E.UnQual (E.Symbol "~>"))) p2) = Rule wt (toRPat p1) (toRPat p2)
toRule _  p                                                        = error $ "toRule: Unsupported: " ++ show p

parseRule wt = toRule wt . E.fromParseResult . E.parseExp

--------------------------------------------------------------------------------

fromRule :: Rule -> E.Exp
fromRule (Rule _ p1 p2) = E.InfixApp (fromRPat p1) (E.QVarOp (E.UnQual (E.Symbol "~>"))) (fromRPat p2)

prettyRule = prettyOneLine . fromRule

--------------------------------------------------------------------------------

mkVarSchemes f = mapM (\(v, t) -> f t >>= \t -> return (s2n v, gen' t))

--------------------------------------------------------------------------------

consT = do
  a <- freshTyVar "a"
  let la = List a
  return $ TyFun a (TyFun la la)
ssT = do
  let c = TyCon "Char"
      s1 = List c
      s2 = List c
  return $ TyFun s1 (TyFun s2 s2)
appendT = do
  a <- freshTyVar "a"
  let la1 = List a
  let la2 = List a
  return $ TyFun la1 (TyFun la2 la2)
listT = do
  [a,b] <- mapM freshTyVar ["a","b"]
  let la = List a
  return $ TyFun b (TyFun (TyFun a (TyFun la b)) (TyFun la b))
dlistT = do
  [a,b] <- mapM freshTyVar ["a","b"]
  let la = List a
      lala = TyFun la la
  return $ TyFun b (TyFun (TyFun a (TyFun lala b)) (TyFun lala  b))

--------------------------------------------------------------------------------

varSchemesInit = mkVarSchemes id
  [("id"                , parseType     "a -> a"                                                        )
  ,("const"             , parseType     "a -> b -> a"                                                   )
  ,("nil"               , parseType     "[a]"                                                           )
  ,("cons"              , consT {-      "a -> [a] -> [a]"                                            -} )
  ,("ss"                , ssT {-        "[Char] -> [Char] -> [Char]"                                 -} )
  ,("append"            , appendT {-    "[a] -> [a] -> [a]"                                          -} )
  ,("compose"           , parseType     "(b -> c) -> (a -> b) -> a -> c"                                )
  ,("length"            , parseType     "[a] -> Int"                                                    )
  ,("print"             , parseType     "[Char] -> a"                                                   )
  ,("foldr"             , parseType     "(a -> b -> b) -> b -> [a] -> b"                                )
  ,("list"              , listT {-      "b -> (a -> [a] -> b) -> [a] -> b"                           -} )
  ,("dlist"             , dlistT {-     "b -> (a -> ([a] -> [a]) -> b) -> ([a] -> [a]) -> b"         -} )
  ,("map"               , parseType     "(a -> b) -> [a] -> [b]"                                        )
  ]

litTypesInit (Int _)     = TyCon <$> return "Int"
litTypesInit (Char _)    = TyCon <$> return "Char"
litTypesInit (String _)  = List <$> (TyCon <$> return "Char")

envInit = Env varSchemesInit litTypesInit

--------------------------------------------------------------------------------

rule_id              = parseRule    0   "M      ~> M"

rule_append2compose  = parseRule    6   "append ~> compose"
rule_ss_app          = parseRule  (-1)  "M      ~> ss (M `as` 1)"
rule_app_nil         = parseRule  (-1)  "M      ~> M (nil `as` 2)"

rule_list2dlist      = parseRule    6   "list   ~> dlist"
rule_nil2id          = parseRule    6   "nil    ~> id"
rule_append_app      = parseRule  (-1)  "M      ~> append (M `as` 1)"
rule_map_append      = parseRule  (-1)  "M      ~> map append (M `as` 1)"

--------------------------------------------------------------------------------

rulesStrings = [rule_append2compose, rule_id, rule_ss_app, rule_app_nil]

transformStrings' = transformWith' rulesStrings envInit
transformStrings  = transformWith  rulesStrings envInit

--------------------------------------------------------------------------------

rulesReverse = [rule_append2compose, rule_list2dlist, rule_nil2id, rule_id, rule_append_app, rule_map_append, rule_app_nil]

transformReverse' = transformWith' rulesReverse envInit
transformReverse  = transformWith  rulesReverse envInit

--------------------------------------------------------------------------------

mkExamples = map (\(i, mo) -> (parseExp i, parseExp <$> mo))

examplesStrings = mkExamples
 [ ( "\"abc\""
   , Just $ "\"abc\""
   )
 , ( "\\x -> \"a\""
   , Just $ "\\x -> \"a\""
   )
 , ( "\\x -> x"
   , Just $ "\\x -> x"
   )
 , ( "\\x -> id x"
   , Just $ "\\x -> id x"
   )
 , ( "\\f -> \\x -> f x"
   , Just $ "\\f -> \\x -> f x"
   )
 , ( "\\f -> \\x -> let y = f in y x"
   , Just $ "\\f -> \\x -> let y = f in y x"
   )
 , ( "append \"a\" \"b\""
   , Just $ "compose (ss \"a\") (ss \"b\")"
   )
 , ( "append (cons 1 nil) (cons 2 nil)"
   , Just $ "append (cons 1 nil) (cons 2 nil)"
   )
 , ( "(\\x -> x) (append \"a\" \"b\")"
   , Just $ "(\\x -> x) (compose (ss \"a\") (ss \"b\"))"
   )
 , ( "let x = \"a\" in \"b\""
   , Just $ "let x = \"a\" in \"b\""
   )
 , ( "let x = \"a\" in x"
   , Just $ "let x = \"a\" in x"
   )
 , ( "let x = (\\x -> x) in x"
   , Just $ "let x = (\\x -> x) in x"
   )
 , ( "(let x = (\\x -> x) in x) (append \"a\" \"b\")"
   , Just $ "(let x = (\\x -> x) in x) (compose (ss \"a\") (ss \"b\"))"
   )
 , ( "\\x -> append x"
   , Just $ "\\x -> compose x"
   )
 , ( "\\x -> append x x"
   , Just $ "\\x -> compose x x"
   )
 , ( "\\x -> append x \"b\""
   , Just $ "\\x -> compose x (ss \"b\")"
   )
 , ( "\\x -> append (id x) \"b\""
   , Just $ "\\x -> compose (id x) (ss \"b\")"
   )
 , ( "\\y -> append \"a\" y"
   , Just $ "\\y -> compose (ss \"a\") y"
   )
 , ( "\\x -> \\y -> append \"a\" y"
   , Just $ "\\x -> \\y -> compose (ss \"a\") y"
   )
 , ( "length \"abc\""
   , Just $ "length \"abc\""
   )
 , ( "length (append \"a\" \"b\")"
   , Just $ "length (compose (ss \"a\") (ss \"b\") nil)"
   )
 , ( "length (append \"a\" (append \"b\" \"c\"))"
   , Just $ "length (compose (ss \"a\") (compose (ss \"b\") (ss \"c\")) nil)"
   )
 , ( "id (append \"a\" \"b\")"
   , Just $ "id (compose (ss \"a\") (ss \"b\"))"
   )
 , ( "id 1"
   , Just $ "id 1"
   )
 , ( "foldr append nil"
   , Just $ "foldr compose (ss nil)"
   )
 , ( "length ((foldr append nil) (cons \"a\" (cons \"b\" (cons \"c\" (cons \"d\" nil)))))"
   , Just $ "length ((foldr append nil) (cons \"a\" (cons \"b\" (cons \"c\" (cons \"d\" nil)))))" -- Can add 'map ss'. Higher score leads to more 'ss'.
-- , Just $ "length ((foldr compose (ss nil)) (cons (ss \"a\") (cons (ss \"b\") (cons (ss \"c\") (cons (ss \"d\") nil)))))" -- ALT
   )
 , ( "\\x -> append (append x \"a\") x"
   , Just $ "\\x -> compose (compose x (ss \"a\")) x"
   )
 , ( "\\x -> append (append x \"a\") (id x)"
   , Just $ "\\x -> compose (compose x (ss \"a\")) (id x)"
   )
 , ( "\\x -> append (id x) (id x)"
   , Just $ "\\x -> compose (id x) (id x)"
   )
 , ( "\\x -> let x = append x in compose x"
   , Just $ "\\x -> let x = compose x in compose x"
   )
 , ( "\\x -> let y = append x in append x"
   , Just $ "\\x -> let y = compose x in compose x"
   )
 , ( "fix (\\x -> x)"
   , Just $ "fix (\\x -> x)"
   )
 , ( "fix (\\x -> append \"a\" x)"
   , Just $ "fix (\\x -> compose (ss \"a\") x)"
   )
 , ( "fix (\\x -> id) (append \"a\")"
   , Just $ "fix (\\x -> id) (compose (ss \"a\"))"
   )
 , ( "let f = \\x -> x in const (f 1) (f \"a\")"
   , Just $ "let f = (\\x -> x) in const (f 1) (f \"a\")"
   )
 , ( "(\\x -> append x x) \"a\""
   , Just $ "(\\x -> compose x x) (ss \"a\")"
   )
 , ( "(\\x -> append x \"b\") \"a\""
   , Just $ "(\\x -> compose (ss x) (ss \"b\")) \"a\""
-- , Just $ "(\\x -> compose x (ss \"b\")) (ss \"a\")" -- ALT
   )
 , ( "length ((\\x -> append x x) \"a\")"
   , Just $ "length ((\\x -> compose x x nil) (ss \"a\"))"
-- , Just $ "length ((\\x -> compose x x) (ss \"a\") nil)" -- ALT
   )
 , ( "length ((\\x -> append x (append \"b\" x)) \"a\")"
   , Just $ "length ((\\x -> compose x (compose (ss \"b\") x) nil) (ss \"a\"))"
   )
 , ( "length ((\\x -> append x \"b\") \"a\")"
   , Just $ "length ((\\x -> compose (ss x) (ss \"b\") nil) \"a\")" -- ALT
-- , Just $ "length ((\\x -> compose x (ss \"b\")) (ss \"a\") nil)" -- ALT
-- , Just $ "length ((\\x -> compose x (ss \"b\") nil) (ss \"a\"))" -- ALT
-- , Just $ "length ((\\x -> compose (ss x) (ss \"b\")) \"a\" nil)" -- ALT
--          "length ((\\x -> compose (ss x) (ss \"b\")) nil \"a\")" -- Not allowed
   )
 , ( "let f = \\x -> append x \"b\" in length (f \"a\")"
   , Just $ "let f = \\x -> compose (ss x) (ss \"b\") nil in length (f \"a\")"
-- , Just $ "let f = \\x -> compose x (ss \"b\") in length (f (ss \"a\") nil)" -- ALT
-- , Just $ "let f = \\x -> compose x (ss \"b\") nil in length (f (ss \"a\"))" -- ALT
-- , Just $ "let f = \\x -> compose (ss x) (ss \"b\") in length (f \"a\" nil)" -- ALT
   )
 , ( "let concat = fix (\\r -> list nil (\\x -> \\xs -> append x (r xs))) in concat (cons \"a\" (cons \"b\" nil))"
   , Just $ "let concat = fix (\\r -> list (ss nil) (\\x -> \\xs -> compose (ss x) (r xs))) in concat (cons \"a\" (cons \"b\" nil))"
   )
 , ( "let concat = fix (\\r -> list nil (\\x -> \\xs -> append x (r xs))) in length (concat (cons \"a\" (cons \"b\" nil)))"
   , Just $ "let concat = fix (\\r -> list (ss nil) (\\x -> \\xs -> compose (ss x) (r xs))) in length (concat (cons \"a\" (cons \"b\" nil)) nil)"
   )
 ]

--------------------------------------------------------------------------------

examplesReverse = mkExamples
 [ ( "fix (\\r -> list nil (\\x -> \\xs -> append (r xs) (cons x nil)))"
   , Just $ "fix (\\r -> dlist id (\\x -> \\xs -> compose (r xs) (append (cons x nil))))"
   )
 , ( "let reverse = fix (\\r -> list nil (\\x -> \\xs -> append (r xs) (cons x nil))) in length (reverse (cons 1 (cons 2 nil)))"
   , Just $ "let reverse = fix (\\r -> dlist id (\\x -> \\xs -> compose (r xs) (append (cons x nil)))) in length (reverse (append (cons 1 (cons 2 nil))) nil)"
   )
 , ( "let reverse = fix (\\r -> list nil (\\x -> \\xs -> append (r xs) (cons x nil))) in length (reverse (cons \"a\" (cons \"b\" nil)))"
   , Just $ "let reverse = fix (\\r -> dlist id (\\x -> \\xs -> compose (r xs) (append (cons x nil)))) in length (reverse (append (cons \"a\" (cons \"b\" nil))) nil)"
-- , Just $ "let reverse = fix (\\r -> dlist id (\\x -> \\xs -> compose (r xs) (append (cons (append x) nil)))) in length (reverse (append (cons \"a\" (cons \"b\" nil))) nil) -- Interesting (undesired?, lower weighted) ALT
   )
 , ( "let reverse = fix (\\r -> list nil (\\x -> \\xs -> append (r xs) (cons x nil))) in length (map reverse (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 nil)) nil)))"
   , Just $ "let reverse = fix (\\r -> dlist id (\\x -> \\xs -> compose (r xs) (append (cons x nil)))) in length (map reverse (map append (cons (cons 1 (cons 2 nil)) (cons (cons 3 (cons 4 nil)) nil))))"
   )
 ]

--------------------------------------------------------------------------------

test_inst_gen t = runFreshMT $ t >>= inst . gen'

test_mgu mt1 mt2 = uncurry mgu =<< runFreshMT (do
  t1 <- mt1
  t2 <- mt2
  return (t1, t2))

--------------------------------------------------------------------------------

runFE :: (Monad m) => ErrorT String (FreshMT m) a -> m (Either String a)
runFE = runFreshMT . runErrorT

--------------------------------------------------------------------------------

test_infer e = do
  r <- runFE $ infer envInit (parseExp e)
  case r of
    Left err -> fail err
    Right t  -> putStrLn $ prettyType t

test_infer' e = do
  r <- runFE $ infer envInit (parseExp e)
  case r of
    Left err -> fail err
    Right t  -> print t

--------------------------------------------------------------------------------

test_infer_examples = foldM_ f 0 examplesStrings
  where
    f cnt (e, Nothing) = do
      test cnt e
      return (succ cnt)
    f cnt (e, Just e') = do
      test cnt e
      test cnt e'
      return (succ cnt)
    test cnt e = do
      t <- runFE $ infer envInit e
      case t of
        Right _ -> return ()
        Left err -> putStrLn $ "ERROR(" ++ show cnt ++ "): " ++ prettyExp e ++ " : " ++ err

--------------------------------------------------------------------------------

test_prop_id e = do
  r <- runFE $ prop (\_ _ -> return) envInit (parseExp e)
  case r of
    Left err -> fail err
    Right e' -> print e'

--------------------------------------------------------------------------------

test_prop_id_examples = foldM_ f 0 examplesStrings
  where
    f cnt (e, _) = do
      ir <- runFE $ infer envInit e
      pr <- runFE $ prop (\_ _ -> return) envInit e
      const (succ cnt) <$> case (ir, pr) of
        (Right ti, Right pe)
          | gen' ti == gen' (typeOf pe) -> return ()
          | otherwise -> putStrLn $ "FAIL(" ++ show cnt ++ "): " ++ show ti ++ " vs " ++ show (typeOf pe)
        (Left err , _) -> putStrLn $ "ERROR(" ++ show cnt ++ ") in infer: " ++ err
        (_, Left err) -> putStrLn $ "ERROR(" ++ show cnt ++ ") in prop: " ++ err

--------------------------------------------------------------------------------

test_rewrite r s = runFreshMT $ do
  let e = parseExp s
  e' <- prop (\_ _ -> return) envInit e
  rewrite envInit e' r

--------------------------------------------------------------------------------

mkTestTransform transform s = do
  (e, t) <- transform $ parseExp s
  putStrLn $ prettyExp e ++ " : " ++ prettyType t

mkTestTransformSorted transform' s = do
  es <- liftM sortByWeight . observeAllT . runFreshMT . transform' . parseExp $ s
  mapM_ (\e -> putStr (show (weight e)) >> putStr ": " >> putStr (prettyExp e) >> putStr " : " >> putStrLn (prettyType (typeOf e))) es

mkTestTransformSorted' transform' s =
  liftM sortByWeight . observeAllT . runFreshMT . transform' . parseExp $ s

mkTestTransformMax transform' =
  liftM maxByWeight . observeAllT . runFreshMT . transform' . parseExp

mkTestTransformExamples transform examples = foldM_ f 0 examples
  where
    f cnt (_, Nothing) = return (succ cnt)
    f cnt (e, Just ex) = do
      tx <- runFreshMT $ infer envInit ex
      (e', t') <- transform e
      if ex == e' && gen' tx == gen' t'
        then
          return (succ cnt)
        else do
          putStrLn $ "FAIL(" ++ show cnt ++ "):"
          putStrLn $ "Input Exp     : " ++ prettyExp e
          putStrLn $ "Expected Exp  : " ++ prettyExp ex
          putStrLn $ "Expected Type : " ++ prettyType tx
          putStrLn $ "Result Exp    : " ++ prettyExp e'
          putStrLn $ "Result Type   : " ++ prettyType t'
          return (succ cnt)

--------------------------------------------------------------------------------

test_transformStrings          = mkTestTransform         transformStrings
test_transformStrings_sorted   = mkTestTransformSorted   transformStrings'
test_transformStrings_sorted'  = mkTestTransformSorted'  transformStrings'
test_transformStrings_max      = mkTestTransformMax      transformStrings'
test_transformStrings_examples = mkTestTransformExamples transformStrings examplesStrings

--------------------------------------------------------------------------------

test_transformReverse          = mkTestTransform         transformReverse
test_transformReverse_sorted   = mkTestTransformSorted   transformReverse'
test_transformReverse_sorted'  = mkTestTransformSorted'  transformReverse'
test_transformReverse_max      = mkTestTransformMax      transformReverse'
test_transformReverse_examples = mkTestTransformExamples transformReverse examplesReverse

--------------------------------------------------------------------------------

-- Running time when compiled: 40 minutes
main = do
  test_transformStrings_examples
  test_transformReverse_examples

