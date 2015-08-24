{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Eval where

import Data.Functor.Identity
import Data.ExprGADT.Types
import Data.List (unfoldr)

forbidden :: Expr vs a -> String -> b
forbidden e r = error $ "Impossible branch prevented by type system! " ++ show e ++ " " ++ r

eval :: Expr '[] a -> a
eval = evalWith HNil

evalWith :: forall vs a. HList vs -> Expr vs a -> a
evalWith vs = go
  where
    go :: forall b. Expr vs b -> b
    go e = case reduceAll e of
             V ix                -> subIndexor vs ix
             O0 o                -> op0 o
             O1 o e1             -> onO op1 op1' o (go e1)
             O2 o e1 e2          -> onO op2 op2' o (go e1) (go e2)
             O3 o e1 e2 e3       -> onO op3 op3' o (go e1) (go e2) (go e3)
             Lambda ef           -> \x -> evalWith (x :< vs) ef

subIndexor :: forall ks. HList ks -> (forall v. Indexor ks v -> v)
subIndexor (x :< _ ) IZ      = x
subIndexor (_ :< xs) (IS ix) = subIndexor xs ix
subIndexor HNil      _       = error "Impossible...should be prevented by the type system. There is no Indexor '[] a."


reduceAll :: Expr vs a -> Expr vs a
reduceAll e | e == e'   = e'
            | otherwise = reduceAll e'
  where
    e' = reduceWith V e

reduce :: Expr vs a -> Expr vs a
reduce = reduceWith V

reduceWith :: forall vs us o. (forall v. Indexor vs v -> Expr us v) -> Expr vs o -> Expr us o
reduceWith f = runIdentity . reduceWithA (Identity . f)

reduceWithA :: forall vs us o f. Applicative f => (forall v. Indexor vs v -> f (Expr us v)) -> Expr vs o -> f (Expr us o)
reduceWithA f = reduceWithA' (f' f)
  where
    f' :: forall u vs us. (forall v. Indexor vs v -> f (Expr us v)) -> Expr vs u -> f (Expr us u)
    f' f0 = go
      where
        go :: forall q. Expr vs q -> f (Expr us q)
        go e = case e of
                 V ix -> f0 ix
                 O0 o -> pure $ O0 o
                 O1 o e1 -> O1 o <$> go e1
                 O2 o e1 e2 -> O2 o <$> go e1 <*> go e2
                 O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
                 Lambda ef -> Lambda <$> f' undefined ef

reduceWithA' :: forall vs us o f. Applicative f => (forall v. Expr vs v -> f (Expr us v)) -> Expr vs o -> f (Expr us o)
reduceWithA' f = go
  where
    go :: Expr vs a -> f (Expr us a)
    go e = case e of
             V ix              -> f (V ix)
             O0 o              -> pure $ O0 o
             O1 o e1           -> case o of
                                    Con o'     -> case e1 of
                                                    O0 o'' -> case op1_ o' (op0 o'') of
                                                                Just x -> pure $ O0 x
                                                                _      -> O1 o <$> go e1
                                                    _      -> O1 o <$> go e1
                                    Dec Fst    -> reduceFst e1
                                    Dec Snd    -> reduceSnd e1
             O2 o e1 e2        -> case o of
                                    Con o' -> case (e1, e2) of
                                                (O0 o''1, O0 o''2) -> case op2_ o' (op0 o''1) (op0 o''2) of
                                                                        Just x -> pure $ O0 x
                                                                        _      -> O2 o <$> go e1 <*> go e2
                                                _           -> O2 o <$> go e1 <*> go e2
                                    Dec Ap -> reduceAp e1 e2
             O3 o e1 e2 e3     -> case o of
                                    Con _        -> forbidden e "There aren't even any constructors for Op3.  How absurd."
                                    Dec If       -> reduceIf e1 e2 e3
                                    Dec Case     -> reduceCase e1 e2 e3
                                    Dec UnfoldrN -> reduceUnfoldrN e1 e2 e3
                                    Dec Foldr    -> reduceFoldr e1 e2 e3
             Lambda eλ         -> Lambda <$> go' eλ
    reduceFst :: Expr vs (a, b) -> f (Expr us a)
    reduceFst e' = case e' of
                     O2 (Con Tup) e1 _ -> go e1
                     _                 -> fst' <$> go e'
    reduceSnd :: Expr vs (a, b) -> f (Expr us b)
    reduceSnd e' = case e' of
                     O2 (Con Tup) _ e2 -> go e2
                     _                 -> snd' <$> go e'
    reduceIf :: Expr vs Bool -> Expr vs a -> Expr vs a -> f (Expr us a)
    reduceIf eb ex ey = case eb of
                          O0 (B b) | b         -> go ex
                                   | otherwise -> go ey
                          _                    -> if' <$> go eb <*> go ex <*> go ey
    reduceAp :: forall a b. Expr vs (a -> b) -> Expr vs a -> f (Expr us b)
    reduceAp ef ex = case ef of
                       Lambda eλ -> go (reduceWith apply eλ)
                       _         -> (~$) <$> go ef <*> go ex
      where
        apply :: forall k. Indexor (a ': vs) k -> Expr vs k
        apply IZ      = ex
        apply (IS ix) = V ix
    reduceCase :: forall a b c. Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> f (Expr us c)
    reduceCase ee el er = case ee of
                            O1 (Con Left') ex  -> reduceAp el ex
                            O1 (Con Right') ex -> reduceAp er ex
                            _                  -> case' <$> go ee <*> go el <*> go er
    reduceUnfoldrN :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> f (Expr us [b])
    reduceUnfoldrN en ef ez = case reduce en of
                                O0 (I i) | i <= 0    -> pure nil'
                                         | otherwise -> go (unfold (i - 1))
                                _                    -> unfoldrN' <$> go en <*> go ef <*> go ez
      where
        unfold i = (λ .-> fst' (V IZ) ~: unfoldrN' (iI i)
                                                   (pushInto ef)
                                                   (snd' (V IZ))
                   ) ~$ (ef ~$ ez)
    reduceFoldr :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> f (Expr us b)
    reduceFoldr ef ez exs = case reduce exs of
                              O0 Nil               -> go ez
                              O2 (Con Cons) ey eys -> go $ ef ~$ ey
                                                              ~$ foldr' ef ez eys
                              _                    -> foldr' <$> go ef <*> go ez <*> go exs
    go' :: forall d a. Expr (d ': vs) a -> f (Expr (d ': us) a)
    go' = reduceWithA' f'
      where
        f' :: forall k. Expr (d ': vs) k  -> f (Expr (d ': us) k)
        f' (V ix) = case ix of
                      IZ -> pure $ V IZ
                      IS ix' -> shuffleVars IS <$> f (V ix')
        f' e      = go' e
        -- f' (IS ix) = shuffleVars IS <$> f ix

shuffleVars :: forall ks js a. (forall k. Indexor ks k -> Indexor js k) -> Expr ks a -> Expr js a
shuffleVars f = runIdentity . shuffleVarsA (pure . f)

shuffleVarsA :: forall ks js a f. Applicative f => (forall k. Indexor ks k -> f (Indexor js k)) -> Expr ks a -> f (Expr js a)
shuffleVarsA f = go
  where
    go :: forall b. Expr ks b -> f (Expr js b)
    go e = case e of
             V ix -> V <$> f ix
             O0 o -> pure $ O0 o
             O1 o e1 -> O1 o <$> go e1
             O2 o e1 e2 -> O2 o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
             Lambda ef -> Lambda <$> shuffleVarsA f' ef
    f' :: forall b c. Indexor (c ': ks) b -> f (Indexor (c ': js) b)
    f' IZ      = pure IZ
    f' (IS ix) = IS <$> f ix

-- will this be good enough for monomorphic cases?
-- might have to resort to doing something with Proxy and letting people
-- manually state.
--
-- looks like it defers to "push as much as possible", which maybe or maybe
-- not be the best desire for monomorphic code...

class PushInto vs us where
    pushInto :: Expr vs a -> Expr us a

instance PushInto vs vs where
    pushInto = id

instance PushInto vs us => PushInto vs (v ': us) where
    pushInto = shuffleVars IS . pushInto

-- gives a pushing function for each layer introduced
-- doesn't look good because requres $ cause existentials, so can't use .->
-- and pretty stuff like that :(
λ' :: ((forall c. Expr vs c -> Expr (a ': vs) c)
   -> Expr (a ': vs) b)
   -> Expr vs (a -> b)
λ' toPush = λ .-> toPush (shuffleVars IS)

-- gives a pushing function
lambda' :: ((forall c. Expr vs c -> Expr (a ': vs) c)
        -> Expr (a ': vs) b)
        -> Expr vs (a -> b)
lambda' = λ'

op0 :: Op0 a -> a
op0 (I i) = i
op0 (B b) = b
op0 Nil   = []
op0 Unit  = ()

op1 :: Op1 a b -> a -> b
op1 Abs    = abs
op1 Signum = signum
op1 Not    = not
op1 Left'  = Left
op1 Right' = Right

op1_ :: Op1 a b -> a -> Maybe (Op0 b)
op1_ o = modder . op1 o
  where
    modder = case o of
               Abs    -> Just . I
               Signum -> Just . I
               Not    -> Just . B
               Left'  -> const Nothing
               Right' -> const Nothing

op1' :: Op1' a b -> a -> b
op1' Fst = fst
op1' Snd = snd

op2 :: Op2 a b c -> a -> b -> c
op2 Plus    = (+)
op2 Times   = (*)
op2 Minus   = (-)
op2 Div     = \x y -> if y == 0 then Left () else Right (x `div` y)
op2 Mod     = \x y -> if y == 0 then Left () else Right (x `mod` y)
op2 LEquals = (<=)
op2 And     = (&&)
op2 Or      = (||)
op2 Tup     = (,)
op2 Cons    = (:)

op2_ :: Op2 a b c -> a -> b -> Maybe (Op0 c)
op2_ o x y = modder (op2 o x y)
  where
    modder = case o of
               Plus    -> Just . I
               Times   -> Just . I
               Minus   -> Just . I
               LEquals -> Just . B
               And     -> Just . B
               Or      -> Just . B
               Tup     -> const Nothing
               Cons    -> const Nothing
               Div     -> const Nothing
               Mod     -> const Nothing

op2' :: Op2' a b c -> a -> b -> c
op2' Ap = ($)

op3 :: Op3 a b c d -> a -> b -> c -> d
op3 = error "No constructors of Op3.  How absurd!"

op3' :: Op3' a b c d -> a -> b -> c -> d
op3' If       = \b x y -> if b then x else y
op3' Case     = \e l r -> either l r e
op3' UnfoldrN = \n f z -> take n $ unfoldr (Just . f) z
op3' Foldr    = foldr

lengthHList :: HList vs -> Int
lengthHList HNil = 0
lengthHList (_ :< xs) = 1 + lengthHList xs

