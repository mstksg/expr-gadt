{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.ExprGADT.Dumb.Infer where

-- import Control.Exception
-- import Control.Arrow
-- import Control.Monad.Except
-- import Control.Monad.RWS
-- import Data.ExprGADT.Dumb.Types
-- import Data.Typeable
-- import Data.ExprGADT.Types
-- import Data.List                (nub)
-- import Data.Map                 (Map)
-- import Data.Set                 (Set)
-- import qualified Data.Map       as M
-- import qualified Data.Set       as S

-- data Scheme = Forall [TVar] TExpr
--             deriving (Show, Eq)

-- newtype InferState = InferState { count :: Int }

-- newtype Subst = Subst (Map TVar TExpr)

-- instance Monoid Subst where
--     mempty = Subst M.empty
--     mappend (Subst x) (Subst y) = Subst $ fmap apl y `M.union` x
--       where
--         apl = applyTExpr (Subst x)

-- type Constraint = (TExpr, TExpr)
-- type Unifier = (Subst, [Constraint])

-- data Env = Env { envTypes :: Map VName Scheme }

-- instance Monoid Env where
--     mempty = Env M.empty
--     mappend (Env x) (Env y) = Env (M.union x y)

-- data TypeError :: * where
--     TErrUnbound :: VName -> TypeError
--     TErrInfType :: TVar -> TExpr -> TypeError
--     TErrMismatch :: [TExpr] -> [TExpr] -> TypeError
--     TErrUniFail :: TExpr -> TExpr -> TypeError
--     TErrBottom :: TypeError
--   deriving (Show, Typeable)

-- instance Exception TypeError

-- varNames :: [VName]
-- varNames = [ v : if n == 0 then "" else show (n :: Int)
--            | n <- [0..]
--            , v <- "xyzhijklmnpqrstuvw"]

-- runInfer :: Env -> RWST Env [Constraint] [VName] (Either TypeError) TExpr -> Either TypeError (TExpr, [Constraint])
-- runInfer env m = evalRWST m env varNames

-- inferExpr :: Env -> DumbExpr -> Either TypeError Scheme
-- inferExpr env ex = do
--     (ty, cs) <- runInfer env (infer ex)
--     subst <- solver (mempty, cs)
--     return $ closeOver (applyTExpr subst ty)
--   where
--     closeOver = normalize . generalize (Env M.empty)
--     normalize (Forall _ body) = Forall (map snd ord') (normtype body)
--       where
--         ord' = zip (nub (fv body)) (map TV varNames)
--         fv (TEV a) = [a]
--         fv (TEO0 _) = []
--         fv (TEO1 _ e1) = fv e1
--         fv (TEO2 _ e1 e2) = fv e1 ++ fv e2

--         normtype (TEO0 o) = TEO0 o
--         normtype (TEO1 o e1) = TEO1 o (normtype e1)
--         normtype (TEO2 o e1 e2) = TEO2 o (normtype e1) (normtype e2)
--         normtype (TEV v) = case lookup v ord' of
--                              Just x -> TEV x
--                              Nothing -> error "type variable not in signature, what gives"
--     generalize env' t = Forall as t
--       where
--         as = S.toList $ ftvTExpr t `S.difference` ftvEnv env'
--         ftvEnv = S.unions . map ftvScheme . M.elems . envTypes
--     ftvScheme (Forall as t) = ftvTExpr t `S.difference` S.fromList as


-- infer :: (MonadError TypeError m, MonadReader Env m, MonadState [VName] m, MonadWriter [Constraint] m)
--       => DumbExpr -> m TExpr
-- infer e = case e of
--             DV v -> lookupEnv v
--             DO0 o -> case o of
--                        I _ -> pure tInt
--                        B _ -> pure tBool
--                        Unit -> pure (TEO0 TOUnit)
--                        Nil -> do
--                          t1 <- fresh
--                          tv <- fresh
--                          uni (TEO1 TOList t1) tv
--                          return tv
--             DO1 o e1 -> do
--               t1 <- infer e1
--               tv <- fresh
--               let u1 = t1 `tFunc` tv
--               u2 <- case o of
--                       Abs    -> return $ tInt `tFunc` tInt
--                       Signum -> return $ tInt `tFunc` tInt
--                       Not    -> return $ tBool `tFunc` tBool
--                       Left'  -> do
--                         tr <- fresh
--                         return $ t1 `tFunc` TEO2 TOEither t1 tr
--                       Right' -> do
--                         tl <- fresh
--                         return $ t1 `tFunc` TEO2 TOEither tl t1
--                       Fst    -> do
--                         tfst <- fresh
--                         tsnd <- fresh
--                         uni t1 (TEO2 TOTuple tfst tsnd)
--                         return $ t1 `tFunc` tfst
--                       Snd    -> do
--                         tfst <- fresh
--                         tsnd <- fresh
--                         uni t1 (TEO2 TOTuple tfst tsnd)
--                         return $ t1 `tFunc` tsnd
--               uni u1 u2
--               return tv
--             DO2 o e1 e2 -> do
--               t1 <- infer e1
--               t2 <- infer e2
--               tv <- fresh
--               let u1 = t1 `tFunc` (t2 `tFunc` tv)
--               u2 <- case o of
--                       Plus    -> return $ tInt `tFunc` (tInt `tFunc` tInt)
--                       Times   -> return $ tInt `tFunc` (tInt `tFunc` tInt)
--                       Minus   -> return $ tInt `tFunc` (tInt `tFunc` tInt)
--                       LEquals -> return $ tInt `tFunc` (tInt `tFunc` tBool)
--                       And     -> return $ tBool `tFunc` (tBool `tFunc` tBool)
--                       Or      -> return $ tBool `tFunc` (tBool `tFunc` tBool)
--                       Tup     -> return $ t1 `tFunc` (t2 `tFunc` TEO2 TOTuple t1 t2)
--                       Cons    -> return $ t1 `tFunc` (TEO1 TOList t1 `tFunc` TEO1 TOList t1)
--                       Ap      -> do
--                         t3 <- fresh
--                         uni t1 (TEO2 TOFunc t2 t3)
--                         return $ t1 `tFunc` (t2 `tFunc` t3)
--                       Div     -> return $ tInt `tFunc` (tInt `tFunc` TEO2 TOEither (TEO0 TOUnit) tInt)
--                       Mod     -> return $ tInt `tFunc` (tInt `tFunc` TEO2 TOEither (TEO0 TOUnit) tInt)
--               uni u1 u2
--               return tv
--             DO3 o e1 e2 e3 -> do
--               t1 <- infer e1
--               t2 <- infer e2
--               t3 <- infer e3
--               tv <- fresh
--               let u1 = t1 `tFunc` (t2 `tFunc` (t3 `tFunc` tv))
--               u2 <- case o of
--                       If -> do
--                         uni t2 t3
--                         return $ tBool `tFunc` (t2 `tFunc` (t2 `tFunc` t2))
--                       Case -> do
--                         ta <- fresh
--                         tb <- fresh
--                         tc <- fresh
--                         uni t2 (ta `tFunc` tc)
--                         uni t3 (tb `tFunc` tc)
--                         uni t1 (TEO2 TOEither ta tb)
--                         return $ t1 `tFunc` (t2 `tFunc` (t3 `tFunc` tc))
--                       UnfoldrN -> do
--                         tb <- fresh
--                         uni t2 (t3 `tFunc` TEO2 TOTuple tb t3)
--                         return $ tInt `tFunc` (t2 `tFunc` (t3 `tFunc` TEO1 TOList tb))
--                       Foldr -> do
--                         ta <- fresh
--                         uni t1 (ta `tFunc` (t2 `tFunc` t2))
--                         uni t3 (TEO1 TOList ta)
--                         return $ t1 `tFunc` (t2 `tFunc` (t3 `tFunc` t2))
--               uni u1 u2
--               return tv
--             DLambda x e1 -> do
--               tv <- fresh
--               t <- inEnv (x, Forall [] tv) (infer e1)
--               return (tv `tFunc` t)
--   where
--     tInt = TEO0 TOInt
--     tBool = TEO0 TOBool
--     tFunc = TEO2 TOFunc
--     uni :: MonadWriter [Constraint] m => TExpr -> TExpr -> m ()
--     uni t1 t2 = tell [(t1, t2)]
--     lookupEnv :: (MonadState [VName] m, MonadError TypeError m, MonadReader Env m) => VName -> m TExpr
--     lookupEnv x = do
--         Env env <- ask
--         case M.lookup x env of
--           Nothing -> throwError $ TErrUnbound x
--           Just t -> instantiate t
--     instantiate :: MonadState [VName] m => Scheme -> m TExpr
--     instantiate (Forall as t) = do
--         as' <- mapM (const fresh) as
--         let s = Subst $ M.fromList (zip as as')
--         return $ applyTExpr s t
--     inEnv :: MonadReader Env m => (VName, Scheme) -> m a -> m a
--     inEnv (x, sc) = local $ \e' -> remove e' x `extend` (x, sc)
--     extend :: Env -> (VName, Scheme) -> Env
--     extend env (x, s) = env { envTypes = M.insert x s (envTypes env) }
--     remove :: Env -> VName -> Env
--     remove (Env env) x = Env (M.delete x env)

-- fresh :: MonadState [VName] m => m TExpr
-- fresh = state $ \(x:xs) -> (TEV (TV x), xs)

-- applyTExpr :: Subst -> TExpr -> TExpr
-- applyTExpr s@(Subst m) t = case t of
--                              TEO0 a -> TEO0 a
--                              TEV v -> M.findWithDefault t v m
--                              TEO1 o e1 -> TEO1 o (applyTExpr s e1)
--                              TEO2 o e1 e2 -> TEO2 o (applyTExpr s e1) (applyTExpr s e2)

-- solver :: MonadError TypeError m => Unifier -> m Subst
-- solver (su, cs) = case cs of
--                     [] -> pure su
--                     ((t1, t2): cs0) -> do
--                       su1 <- unifies t1 t2
--                       solver (su1 <> su, map (applyTExpr su1 *** applyTExpr su1) cs0)

-- unifies :: MonadError TypeError m => TExpr -> TExpr -> m Subst
-- unifies t1 t2 | t1 == t2 = pure mempty
-- unifies (TEV v) t = v `bind` t
-- unifies t (TEV v) = v `bind` t
-- unifies (TEO1 _ t1) (TEO1 _ t2) = unifies t1 t2
-- unifies (TEO2 _ t1 t2) (TEO2 _ t3 t4) = unifyMany [t1, t2] [t3, t4]
-- unifies t1 t2 = throwError $ TErrUniFail t1 t2

-- unifyMany :: MonadError TypeError m => [TExpr] -> [TExpr] -> m Subst
-- unifyMany [] [] = pure mempty
-- unifyMany (t1:ts1) (t2:ts2) = do
--     su1 <- unifies t1 t2
--     su2 <- unifyMany (applyTExpr su1 <$> ts1) (applyTExpr su1 <$> ts2)
--     return (su2 <> su1)
-- unifyMany t1 t2 = throwError $ TErrMismatch t1 t2

-- bind :: MonadError TypeError m => TVar -> TExpr -> m Subst
-- bind a t | t == TEV a      = pure mempty
--          | occursCheck a t = throwError $ TErrInfType a t
--          | otherwise       = pure (Subst (M.singleton a t))
--   where
--     occursCheck a' t' = a' `S.member` ftvTExpr t'

-- ftvTExpr :: TExpr -> Set TVar
-- ftvTExpr t' = case t' of
--                 TEV a' -> S.singleton a'
--                 TEO0 _ -> S.empty
--                 TEO1 _ t1 -> ftvTExpr t1
--                 TEO2 _ t1 t2 -> ftvTExpr t1 `S.union` ftvTExpr t2
