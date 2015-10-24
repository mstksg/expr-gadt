{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Traversals where

import Data.ExprGADT.Types
import Data.Type.Product
import Data.Monoid
import Type.Class.HFunctor
import Data.Functor.Identity

over' :: ((a -> Identity b) -> c -> Identity d) -> (a -> b) -> c -> d
over' l f = runIdentity . l (Identity . f)

overRN :: ((forall a. p a -> Identity (r a)) -> c -> Identity d) -> (forall a. p a -> r a) -> c -> d
overRN l f = runIdentity . l (Identity . f)

overRN2 :: ((forall a b. p a b -> Identity (r a b)) -> c -> Identity d) -> (forall a b. p a b -> r a b) -> c -> d
overRN2 l f = runIdentity . l (Identity . f)

traverseIntLeaves :: forall vs a f. Applicative f
                  => (Int -> f (Expr vs Int))
                  -> Expr vs a
                  -> f (Expr vs a)
traverseIntLeaves f = traverseExprO0 f'
  where
    f' :: forall ts b. Op0 ts b -> f (Expr vs b)
    f' (I i) = f i
    f' o     = pure $ o0 o

traverseBoolLeaves :: forall vs a f. Applicative f
                   => (Bool -> f (Expr vs Bool))
                   -> Expr vs a
                   -> f (Expr vs a)
traverseBoolLeaves f = traverseExprO0 f'
  where
    f' :: forall ts b. Op0 ts b -> f (Expr vs b)
    f' (B b) = f b
    f' o     = pure $ o0 o

traverseUnitLeaves :: forall vs a f. Applicative f
                   => f (Expr vs ())
                   -> Expr vs a
                   -> f (Expr vs a)
traverseUnitLeaves f = traverseExprO0 f'
  where
    f' :: forall ts b. Op0 ts b -> f (Expr vs b)
    f' Unit = f
    f' o    = pure $ o0 o

-- find a way to traverse explicitly non-leaves?  or maybe all O2's...or
-- O2's only if they don't contain any more O2's ?  O2's all the way down?
-- O2's all the way down would definitely require Monad.

type ExprLeaf ts vs a = Either (Indexor vs a) (Op0 ts a)

-- overExprLeaves :: forall vs a. (forall us b. ExprLeaf us b -> Expr us b) -> Expr vs a -> Expr vs a
-- overExprLeaves f = runIdentity . traverseExprLeaves (Identity . f)

traverseExprLeaves :: forall vs a f. Applicative f
                   => (forall ts us b. ExprLeaf ts us b -> f (Expr us b))
                   -> Expr vs a
                   -> f (Expr vs a)
traverseExprLeaves f = go
  where
    go :: forall b. Expr vs b -> f (Expr vs b)
    go e = case e of
             V ix          -> f (Left ix)
             O o Ø         -> f (Right o)
             O o es        -> O o <$> traverse' go es
             Lambda ef     -> Lambda <$> traverseExprLeaves f ef

traverseExprO0 :: forall vs a f. Applicative f
               => (forall ts b. Op0 ts b -> f (Expr vs b))
               -> Expr vs a
               -> f (Expr vs a)
traverseExprO0 f = go
  where
    go :: forall b. Expr vs b -> f (Expr vs b)
    go e = case e of
             V ix          -> pure $ V ix
             O o Ø         -> f o
             O o es        -> O o <$> traverse' go es
             Lambda ef     -> Lambda <$> traverseExprO0 (fmap (overIxors IS) . f) ef

overIxors :: forall ks js a. (forall k. Indexor ks k -> Indexor js k) -> Expr ks a -> Expr js a
overIxors = overRN traverseIxors

traverseIxors :: forall ks js a f. Applicative f
              => (forall k. Indexor ks k -> f (Indexor js k))
              -> Expr ks a
              -> f (Expr js a)
traverseIxors f = go
  where
    go :: forall b. Expr ks b -> f (Expr js b)
    go e = case e of
             V ix      -> V <$> f ix
             O o es    -> O o <$> traverse' go es
             Lambda ef -> Lambda <$> traverseIxors f' ef
    f' :: forall b c. Indexor (c ': ks) b -> f (Indexor (c ': js) b)
    f' IZ      = pure IZ
    f' (IS ix) = IS <$> f ix

overIxorsP :: forall ks js a. (forall k. Indexor ks k -> Indexor js k) -> ExprP ks a -> ExprP js a
overIxorsP = overRN traverseIxorsP

traverseIxorsP :: forall ks js a f. Applicative f
               => (forall k. Indexor ks k -> f (Indexor js k))
               -> ExprP ks a
               -> f (ExprP js a)
traverseIxorsP f = go
  where
    go :: forall b. ExprP ks b -> f (ExprP js b)
    go e = case e of
             VP ix         -> VP <$> f ix
             TP t          -> pure (TP t)
             OP o ts es    -> OP o <$> traverse' go ts <*> traverse' go es
             LambdaP et eλ -> LambdaP <$> go et <*> traverseIxorsP f' eλ
    f' :: forall b c. Indexor (c ': ks) b -> f (Indexor (c ': js) b)
    f' IZ      = pure IZ
    f' (IS ix) = IS <$> f ix


subIxors :: forall vs us a.
            (forall b. Indexor vs b -> Expr us b)
          -> Expr vs a
          -> Expr us a
subIxors = overRN subIxorsA

subIxorsA :: forall vs us f a. Applicative f
          => (forall b. Indexor vs b -> f (Expr us b))
          -> Expr vs a
          -> f (Expr us a)
subIxorsA f = go
  where
    go :: forall b. Expr vs b -> f (Expr us b)
    go e = case e of
             V ix      -> f ix
             O o es    -> O o <$> traverse' go es
             Lambda eλ -> Lambda <$> subIxorsA f' eλ
    f' :: forall b c. Indexor (c ': vs) b -> f (Expr (c ': us) b)
    f' IZ      = pure $ V IZ
    f' (IS ix) = subIxors (V . IS) <$> f ix

subIxorsP :: forall vs us a.
             (forall b. Indexor vs b -> ExprP us b)
           -> ExprP vs a
           -> ExprP us a
subIxorsP = overRN subIxorsAP

subIxorsAP :: forall vs us f a. Applicative f
           => (forall b. Indexor vs b -> f (ExprP us b))
           -> ExprP vs a
           -> f (ExprP us a)
subIxorsAP f = go
  where
    go :: forall b. ExprP vs b -> f (ExprP us b)
    go e = case e of
             VP ix         -> f ix
             TP t          -> pure (TP t)
             OP o ts es    -> OP o <$> traverse' go ts <*> traverse' go es
             LambdaP et eλ -> LambdaP <$> go et <*> subIxorsAP f' eλ
    f' :: forall b c. Indexor (c ': vs) b -> f (ExprP (c ': us) b)
    f' IZ      = pure $ VP IZ
    f' (IS ix) = subIxorsP (VP . IS) <$> f ix



traverseExprPostM :: forall vs a m. Monad m
                  => (forall b us. Expr us b -> m (Expr us b))
                  -> Expr vs a
                  -> m (Expr vs a)
traverseExprPostM f = go
  where
    go :: forall us b. Expr us b -> m (Expr us b)
    go e = case e of
             V _           -> f e
             O o es -> do
               es' <- traverse' go es
               f (O o es')
             Lambda eλ     -> do
               eλ' <- go eλ
               f $ Lambda eλ'

-- TODO: PR to type-combinators
traverse'_ :: (Applicative h, HFoldable t)
           => (forall a. f a -> h c)
           -> t f b
           -> h ()
traverse'_ f xs = flip appEndo (pure ())
                $ foldMap' (\x -> Endo $ \y -> f x *> y) xs

traverseExprPost_ :: forall vs a c f. Applicative f
                  => (forall b us. Expr us b -> f c)
                  -> Expr vs a
                  -> f ()
traverseExprPost_ f = go
  where
    go :: forall b us. Expr us b -> f ()
    go e = (case e of
              V _       -> pure ()
              O _ es    -> traverse'_ f es
              Lambda eλ -> go eλ
           ) <* f e

traverseExprPre_ :: forall vs a c f. Applicative f => (forall b us. Expr us b -> f c) -> Expr vs a -> f ()
traverseExprPre_ f = go
  where
    go :: forall b us. Expr us b -> f ()
    go e = f e *> case e of
                    V _       -> pure ()
                    O _ es    -> traverse'_ f es
                    Lambda eλ -> go eλ

traverseExprPreM :: forall vs a m. Monad m
                 => (forall b us. Expr us b -> m (Expr us b))
                 -> Expr vs a
                 -> m (Expr vs a)
traverseExprPreM f = go
  where
    go :: forall us b. Expr us b -> m (Expr us b)
    go e = do
      e' <- f e
      case e' of
        V _       -> return e'
        O o es    -> O o <$> traverse' go es
        Lambda eλ -> Lambda <$> go eλ

traverseExprPrePostM :: forall vs a m. Monad m
                     => (forall b us. Expr us b -> m (Expr us b))
                     -> Expr vs a
                     -> m (Expr vs a)
traverseExprPrePostM f = go
  where
    go :: forall us b. Expr us b -> m (Expr us b)
    go e = do
      e' <- f e
      case e' of
        V _       -> return e'
        O o es    -> do
          es' <- traverse' go es
          f (O o es')
        Lambda eλ -> do
          eλ' <- go eλ
          f $ Lambda eλ'
