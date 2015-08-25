{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Data.ExprGADT.Traversals where

import Data.Functor.Identity
import Debug.Trace
import Data.Typeable
import Data.ExprGADT.Types
import Data.ExprGADT.Eval
import Data.Profunctor as P

traverseIntLeaves :: forall vs a f. Applicative f => (Int -> f (Expr vs Int)) -> Expr vs a -> f (Expr vs a)
traverseIntLeaves f = traverseExprLeaves f'
  where
    f' :: forall b. ExprLeaf vs b -> f (Expr vs b)
    f' (Right (I i)) = f i
    f' (Right o)     = pure $ O0 o
    f' (Left ix)     = pure $ V ix

traverseBoolLeaves :: forall vs a f. Applicative f => (Bool -> f (Expr vs Bool)) -> Expr vs a -> f (Expr vs a)
traverseBoolLeaves f = traverseExprLeaves f'
  where
    f' :: forall b. ExprLeaf vs b -> f (Expr vs b)
    f' (Right (B b)) = f b
    f' (Right o)     = pure $ O0 o
    f' (Left ix)     = pure $ V ix

traverseUnitLeaves :: forall vs a f. Applicative f => f (Expr vs ()) -> Expr vs a -> f (Expr vs a)
traverseUnitLeaves f = traverseExprLeaves f'
  where
    f' :: forall b. ExprLeaf vs b -> f (Expr vs b)
    f' (Right Unit) = f
    f' (Right o)    = pure $ O0 o
    f' (Left ix)    = pure $ V ix

-- find a way to traverse explicitly non-leaves?  or maybe all O2's...or
-- O2's only if they don't contain any more O2's ?  O2's all the way down?
-- O2's all the way down would definitely require Monad.

type ExprLeaf vs a = Either (Indexor vs a) (Op0 a)

traverseExprLeaves :: forall us vs a f. Applicative f => (forall b. ExprLeaf vs b -> f (Expr us b)) -> Expr vs a -> f (Expr us a)
traverseExprLeaves f = go
  where
    go :: forall b. Expr vs b -> f (Expr us b)
    go e = case e of
             V ix -> f (Left ix)
             O0 o -> f (Right o)
             O1 o e1 -> O1 o <$> go e1
             O2 o e1 e2 -> O2 o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
             Lambda ef -> Lambda <$> traverseExprLeaves f' ef

    f' :: forall b c. ExprLeaf (c ': vs) b -> f (Expr (c ': us) b)
    f' (Right o)      = shuffleVars' IS <$> f (Right o)
    f' (Left IZ)      = pure $ V IZ
    f' (Left (IS ix)) = shuffleVars' IS <$> f (Left ix)

shuffleVars' :: forall ks js a. (forall k. Indexor ks k -> Indexor js k) -> Expr ks a -> Expr js a
shuffleVars' f = runIdentity . shuffleVarsA (Identity . f)

shuffleVarsA' :: forall ks js a f. Applicative f => (forall k. Indexor ks k -> f (Indexor js k)) -> Expr ks a -> f (Expr js a)
shuffleVarsA' f = traverseExprLeaves f'
  where
    f' :: forall b. ExprLeaf ks b -> f (Expr js b)
    f' (Left ix) = V <$> f ix
    f' (Right o) = pure $ O0 o

    -- upgrade :: forall t qs rs c. (forall b. Expr qs b -> f (Expr rs b)) -> Expr (t ': qs) c -> f (Expr (t ': rs) c)
    -- upgrade f' = go'
    --   where
    --     go' :: forall d. Expr (t ': qs) d -> f (Expr (t ': rs) d)
    --     go' e = case e of
    --               V IZ -> pure (V IZ)
    --               V (IS ix) -> shuffleVars IS <$> f' (V ix)
    --               O0 o -> pure $ O0 o
    --               O1 o e1 -> O1 o <$> go' e1
    --               O2 o e1 e2 -> O2 o <$> go' e1 <*> go' e2
    --               O3 o e1 e2 e3 -> O3 o <$> go' e1 <*> go' e2 <*> go' e3
    --               Lambda ef -> Lambda <$> upgrade go' ef

data TraversalOrder = PreOrder | PostOrder
                    deriving (Show, Eq, Enum, Read)


-- traverseExpr :: forall vs a m. Monad m => TraversalOrder -> (forall b. Expr vs b -> m (Expr vs b)) -> Expr vs a -> m (Expr vs a)
-- traverseExpr tor f = go
--   where
--     go :: forall b. Expr vs b -> m (Expr vs b)
--     go e = case e of
--              V _ -> f e
--              O0 _ -> f e
--              O1 o e1 -> case tor of
--                           PostOrder -> do
--                             e1' <- go e1
--                             f $ O1 o e1'
--              O2 o e1 e2 -> case tor of
--                              PostOrder -> do
--                                e1' <- go e1
--                                e2' <- go e2
--                                f $ O2 o e1' e2'
--              O3 o e1 e2 e3 -> case tor of
--                                 PostOrder -> do
--                                   e1' <- go e1
--                                   e2' <- go e2
--                                   e3' <- go e3
--                                   f $ O3 o e1' e2' e3'
--              Lambda ef -> case tor of
--                             PostOrder -> do
--                               ef' <- upgrade go ef
--                               f $ Lambda ef'
--     upgrade :: forall t qs c. (forall b. Expr qs b -> m (Expr qs b)) -> Expr (t ': qs) c -> m (Expr (t ': qs) c)
--     upgrade f' = go'
--       where
--         go' :: forall d. Expr (t ': qs) d -> m (Expr (t ': qs) d)
--         go' e = case e of
--                   V IZ -> pure (V IZ)
--                   V (IS ix) -> shuffleVars IS <$> f' (V ix)
--                   O0 o -> pure $ O0 o
--                   O1 o e1 -> O1 o <$> go' e1
--                   O2 o e1 e2 -> O2 o <$> go' e1 <*> go' e2
--                   O3 o e1 e2 e3 -> O3 o <$> go' e1 <*> go' e2 <*> go' e3
--                   Lambda ef -> Lambda <$> upgrade go' ef
--         -- go' e = case e of
--                   -- V IZ -> pure (V IZ)
--                   -- V (IS ix) -> shuffleVars IS <$> f' (V ix)
--                   -- O0 o -> O0 o <$ f' (O0 o)
--                   -- O1 o e1 -> case tor of
--                   --              PostOrder -> do
--                   --                e1' <- go' e1
--                   --                go' $ O1 o e1'
--                   -- O2 o e1 e2 -> case tor of
--                   --                 PostOrder -> do
--                   --                   e1' <- go' e1
--                   --                   e2' <- go' e2
--                   --                   go' $ O2 o e1' e2'
--                   -- O3 o e1 e2 e3 -> case tor of
--                   --                    PostOrder -> do
--                   --                      e1' <- go' e1
--                   --                      e2' <- go' e2
--                   --                      e3' <- go' e3
--                   --                      go' $ O3 o e1' e2' e3'
--                   -- Lambda ef -> case tor of
--                   --                PostOrder -> do
--                   --                  ef' <- upgrade go' ef
--                   --                  go' $ Lambda ef'



-- traverseIx :: Applitive f => (Indexor vs a)

-- over_ :: ((a -> Identity b) -> s -> Identity t) -> (a -> b) -> s -> t
-- over_ l f = runIdentity . l (Identity . f)

                          -- O2 o e1            -> O1 o <$> traverseIntLeaves f e1
                          -- O1 (Con Abs) e1    -> O1 (Con Abs) <$> traverseInts f e1
                          -- O1 (Con Signum) e1 -> O1 (Con Signum) <$>

-- data Op1 :: * -> * -> * where
--     Abs    :: Op1 Int Int
--     Signum :: Op1 Int Int
--     Not    :: Op1 Bool Bool
--     Left'  :: Op1 a (Either a b)
--     Right' :: Op1 b (Either a b)


-- type Prism_ s t a b = forall p f. (Choice p, Applicative f) => p a (f b) -> p s (f t)

-- prism_ :: (b -> t) -> (s -> Either t a) -> Prism_ s t a b
-- prism_ bt seta = dimap seta (either pure (fmap bt)) . P.right'

-- ints :: Prism_ (Expr vs a) (Expr vs a) (Expr us Int) (Expr us Int)
-- ints = prism_ id undefined

    -- V        :: Indexor vs a                   -> Expr vs a
    -- O0       :: Op0 a                          -> Expr vs a
    -- O1       :: O (Op1 a b)     (Op1' a b)     -> Expr vs a        -> Expr vs b
    -- O2       :: O (Op2 a b c)   (Op2' a b c)   -> Expr vs a        -> Expr vs b -> Expr vs c
    -- O3       :: O (Op3 a b c d) (Op3' a b c d) -> Expr vs a        -> Expr vs b -> Expr vs c -> Expr vs d
    -- Lambda   :: Expr (a ': vs) b               -> Expr vs (a -> b)

