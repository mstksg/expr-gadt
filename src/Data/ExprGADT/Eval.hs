{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Eval where

import Debug.Trace
import Data.ExprGADT.Traversals
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
    go e = case e of
             V ix                -> subIndexor vs ix
             O0 o                -> op0 o
             O1 o e1             -> onO op1 op1' o (go e1)
             O2 o e1 e2          -> onO op2 op2' o (go e1) (go e2)
             O3 o e1 e2 e3       -> onO op3 op3' o (go e1) (go e2) (go e3)
             Lambda ef           -> \x -> evalWith (x :< vs) ef

cataLeaves :: forall vs a f. Applicative f => (forall b. ExprLeaf vs b -> f b) -> Expr vs a -> f a
cataLeaves f = go
  where
    go :: forall b. Expr vs b -> f b
    go e = case e of
             V ix          -> f (Left ix)
             O0 o          -> f (Right o)
             O1 o e1       -> onO op1 op1' o <$> go e1
             O2 o e1 e2    -> onO op2 op2' o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> onO op3 op3' o <$> go e1 <*> go e2 <*> go e3
             Lambda ef     -> subber ef
    subber :: forall v b. Expr (v ': vs) b -> f (v -> b)
    subber (V IZ) = pure id
    subber (V (IS ix)) = const <$> f (Left ix)
    subber (O0 o) = const <$> f (Right o)
    subber e = subber e'  -- :'(

subIndexor :: forall ks. HList ks -> (forall v. Indexor ks v -> v)
subIndexor (x :< _ ) IZ      = x
subIndexor (_ :< xs) (IS ix) = subIndexor xs ix
subIndexor HNil      _       = error "Impossible...should be prevented by the type system. There is no Indexor '[] a."

reduceAll :: Expr vs a -> Expr vs a
reduceAll e | e == e'   = e'
            | otherwise = reduceAll e'
  where
    e' = overRN2 traverseExprPrePostM collapse e

collapse :: Expr vs a -> Expr vs a
collapse e = case e of
               V ix -> V ix
               O0 o -> O0 o
               O1 o e1 -> case o of
                            Con o'     -> case e1 of
                                            O0 o'' -> case op1_ o' (op0 o'') of
                                                        Just x -> O0 x
                                                        _      -> O1 o e1
                                            _      -> O1 o e1
                            Dec Fst    -> case e1 of
                                            O2 (Con Tup) ex _ -> ex
                                            _                 -> e
                            Dec Snd    -> case e1 of
                                            O2 (Con Tup) _ ey -> ey
                                            _                 -> e
               O2 o e1 e2 -> case o of
                               Con o' -> case (e1, e2) of
                                           (O0 o''1, O0 o''2) ->
                                             case op2_ o' (op0 o''1) (op0 o''2) of
                                               Just x -> O0 x
                                               _      -> O2 o e1 e2
                                           _   -> e
                               Dec Mod -> collapseModDiv Mod e1 e2
                               Dec Div -> collapseModDiv Div e1 e2
                               Dec Ap  -> collapseAp e1 e2
               O3 o e1 e2 e3 -> case o of
                                  Con _        -> forbidden e "There aren't even any constructors for Op3.  How absurd."
                                  Dec If       -> collapseIf e1 e2 e3
                                  Dec Case     -> collapseCase e1 e2 e3
                                  Dec UnfoldrN -> collapseUnfoldrN e1 e2 e3
                                  Dec Foldr    -> collapseFoldr e1 e2 e3
               Lambda eλ -> Lambda eλ
  where
    collapseModDiv :: Op2' Int Int (Maybe' Int) -> Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
    collapseModDiv o2 ex ey = case (ex, ey) of
                              (O0 (I x), O0 (I y)) -> case op2' o2 x y of
                                                        Left () -> O1 (Con Left') (O0 Unit)
                                                        Right z -> O1 (Con Right') (O0 (I z))
                              _                    -> O2 (Dec o2) ex ey
    collapseAp :: forall vs a b. Expr vs (a -> b) -> Expr vs a -> Expr vs b
    collapseAp ef ex = case ef of
                         Lambda eλ -> subVariables apply eλ
                         _         -> ef ~$ ex
      where
        apply :: forall c. Indexor (a ': vs) c -> Expr vs c
        apply IZ      = ex
        apply (IS ix) = V ix
    collapseIf :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr vs a
    collapseIf eb ex ey = case eb of
                            O0 (B b) | b         -> ex
                                     | otherwise -> ey
                            _                    -> if' eb ex ey
    collapseCase :: Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs c
    collapseCase ee el er = case ee of
                              O1 (Con Left') ex  -> el ~$ ex
                              O1 (Con Right') ex -> er ~$ ex
                              _                  -> case' ee el er
    collapseUnfoldrN :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> Expr vs [b]
    collapseUnfoldrN en ef ez = case en of
                                O0 (I i) | i <= 0    -> nil'
                                         | otherwise -> unfold (i - 1)
                                _                    -> unfoldrN' en ef ez
      where
        unfold i = (λ .-> fst' (V IZ) ~: unfoldrN' (iI i)
                                                   (overIxors IS ef)
                                                   (snd' (V IZ))
                   ) ~$ (ef ~$ ez)
    collapseFoldr :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> Expr vs b
    collapseFoldr ef ez exs = case exs of
                                O0 Nil               -> ez
                                O2 (Con Cons) ey eys -> ef ~$ ey ~$ foldr' ef ez eys
                                _                    -> foldr' ef ez exs

subVariables :: forall vs us a. (forall b. Indexor vs b -> Expr us b) -> Expr vs a -> Expr us a
subVariables f = runIdentity . subVariablesA (Identity . f)

subVariablesA :: forall vs us f a. Applicative f => (forall b. Indexor vs b -> f (Expr us b)) -> Expr vs a -> f (Expr us a)
subVariablesA f = go
  where
    go :: forall b. Expr vs b -> f (Expr us b)
    go e = case e of
             V ix          -> f ix
             O0 o          -> pure $ O0 o
             O1 o e1       -> O1 o <$> go e1
             O2 o e1 e2    -> O2 o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
             Lambda eλ     -> Lambda <$> subVariablesA f' eλ
    f' :: forall b c. Indexor (c ': vs) b -> f (Expr (c ': us) b)
    f' IZ      = pure $ V IZ
    f' (IS ix) = subVariables (V . IS) <$> f ix

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
    pushInto = overIxors IS . pushInto

-- gives a pushing function for each layer introduced
-- doesn't look good because requres $ cause existentials, so can't use .->
-- and pretty stuff like that :(
λ' :: ((forall c. Expr vs c -> Expr (a ': vs) c)
   -> Expr (a ': vs) b)
   -> Expr vs (a -> b)
λ' toPush = λ .-> toPush (overIxors IS)

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

op2' :: Op2' a b c -> a -> b -> c
op2' Ap  = ($)
op2' Div = \x y -> if y == 0 then Left () else Right (x `div` y)
op2' Mod = \x y -> if y == 0 then Left () else Right (x `mod` y)

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

