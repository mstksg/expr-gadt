{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Data.ExprGADT.Traversals where

import Data.Functor.Identity
import Debug.Trace
import Data.Typeable
import Data.ExprGADT.Eval
import Data.ExprGADT.Types
import Data.ExprGADT.Eval
import Data.Profunctor as P

traverseIntLeaves :: forall vs a f. Applicative f => (Int -> f (Expr vs Int)) -> Expr vs a -> f (Expr vs a)
traverseIntLeaves f = traverseExprO0 f'
  where
    f' :: forall b. Op0 b -> f (Expr vs b)
    f' (I i) = f i
    f' o     = pure $ O0 o

traverseBoolLeaves :: forall vs a f. Applicative f => (Bool -> f (Expr vs Bool)) -> Expr vs a -> f (Expr vs a)
traverseBoolLeaves f = traverseExprO0 f'
  where
    f' :: forall b. Op0 b -> f (Expr vs b)
    f' (B b) = f b
    f' o     = pure $ O0 o

traverseUnitLeaves :: forall vs a f. Applicative f => f (Expr vs ()) -> Expr vs a -> f (Expr vs a)
traverseUnitLeaves f = traverseExprO0 f'
  where
    f' :: forall b. Op0 b -> f (Expr vs b)
    f' Unit = f
    f' o    = pure $ O0 o

-- find a way to traverse explicitly non-leaves?  or maybe all O2's...or
-- O2's only if they don't contain any more O2's ?  O2's all the way down?
-- O2's all the way down would definitely require Monad.

type ExprLeaf vs a = Either (Indexor vs a) (Op0 a)

traverseExprLeaves :: forall vs a f. Applicative f => (forall us b. ExprLeaf us b -> f (Expr us b)) -> Expr vs a -> f (Expr vs a)
traverseExprLeaves f = go
  where
    go :: forall b. Expr vs b -> f (Expr vs b)
    go e = case e of
             V ix -> f (Left ix)
             O0 o -> f (Right o)
             O1 o e1 -> O1 o <$> go e1
             O2 o e1 e2 -> O2 o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
             Lambda ef -> Lambda <$> traverseExprLeaves f ef

traverseExprO0 :: forall vs a f. Applicative f => (forall b. Op0 b -> f (Expr vs b)) -> Expr vs a -> f (Expr vs a)
traverseExprO0 f = go
  where
    go :: forall b. Expr vs b -> f (Expr vs b)
    go e = case e of
             V ix -> pure $ V ix
             O0 o -> f o
             O1 o e1 -> O1 o <$> go e1
             O2 o e1 e2 -> O2 o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
             Lambda ef -> Lambda <$> traverseExprO0 (fmap (shuffleVars IS) . f) ef

traverseExprPostM :: forall vs a m. Monad m => (forall b us. Expr us b -> m (Expr us b)) -> Expr vs a -> m (Expr vs a)
traverseExprPostM f = go
  where
    go :: forall us b. Expr us b -> m (Expr us b)
    go e = case e of
             V _  -> f e
             O0 _ -> f e
             O1 o e1 -> do
               e1' <- go e1
               f $ O1 o e1'
             O2 o e1 e2 -> do
               e1' <- go e1
               e2' <- go e2
               f $ O2 o e1' e2'
             O3 o e1 e2 e3 -> do
               e1' <- go e1
               e2' <- go e2
               e3' <- go e3
               f $ O3 o e1' e2' e3'
             Lambda eλ -> do
               eλ' <- go eλ
               f $ Lambda eλ'

traverseExprPost_ :: forall vs a f. Applicative f => (forall b us. Expr us b -> f ()) -> Expr vs a -> f ()
traverseExprPost_ f = go
  where
    go :: forall b us. Expr us b -> f ()
    go e = (case e of
              V _ -> pure ()
              O0 _ -> pure ()
              O1 _ e1 -> go e1
              O2 _ e1 e2 -> go e1 *> go e2
              O3 _ e1 e2 e3 -> go e1 *> go e2 *> go e3
              Lambda eλ -> go eλ
           ) *> f e

traverseExprPre_ :: forall vs a f. Applicative f => (forall b us. Expr us b -> f ()) -> Expr vs a -> f ()
traverseExprPre_ f = go
  where
    go :: forall b us. Expr us b -> f ()
    go e = f e *> case e of
                    V _ -> pure ()
                    O0 _ -> pure ()
                    O1 _ e1 -> go e1
                    O2 _ e1 e2 -> go e1 *> go e2
                    O3 _ e1 e2 e3 -> go e1 *> go e2 *> go e3
                    Lambda eλ -> go eλ

