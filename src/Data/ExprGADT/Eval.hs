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
    e' = collapse e

reduce :: Expr vs a -> Expr vs a
reduce = collapse

collapse :: forall vs a. Expr vs a -> Expr vs a
collapse e = case e of
               V ix              -> V ix
               O0 o              -> O0 o
               O1 o e1           -> case o of
                                      Con o'     -> case e1 of
                                                      O0 o'' -> case op1_ o' (op0 o'') of
                                                                  Just x -> O0 x
                                                                  _      -> O1 o (collapse e1)
                                                      _      -> O1 o (collapse e1)
                                      Dec Fst    -> collapseFst e1
                                      Dec Snd    -> collapseSnd e1
               O2 o e1 e2        -> case o of
                                      Con o' -> case (e1, e2) of
                                                  (O0 o''1, O0 o''2) ->
                                                    case op2_ o' (op0 o''1) (op0 o''2) of
                                                      Just x -> O0 x
                                                      _      -> O2 o (collapse e1) (collapse e2)
                                                  _   -> O2 o (collapse e1) (collapse e2)
                                      Dec Mod -> collapseModDiv Mod e1 e2
                                      Dec Div -> collapseModDiv Div e1 e2
                                      Dec Ap  -> collapseAp e1 e2
               O3 o e1 e2 e3     -> case o of
                                      Con _        -> forbidden e "There aren't even any constructors for Op3.  How absurd."
                                      Dec If       -> collapseIf e1 e2 e3
                                      Dec Case     -> collapseCase e1 e2 e3
                                      Dec UnfoldrN -> collapseUnfoldrN e1 e2 e3
                                      Dec Foldr    -> collapseFoldr e1 e2 e3
               Lambda eλ         -> Lambda (collapse eλ)
  where
    collapseFst :: Expr vs (b, c) -> Expr vs b
    collapseFst e' = case collapse e' of
                       O2 (Con Tup) e1 _ -> collapse e1
                       _                 -> fst' (collapse e')
    collapseSnd :: Expr vs (b, c) -> Expr vs c
    collapseSnd e' = case collapse e' of
                       O2 (Con Tup) _ e2 -> collapse e2
                       _                 -> snd' (collapse e')
    collapseModDiv :: Op2' Int Int (Maybe' Int) -> Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
    collapseModDiv o2 ex ey = case (ex, ey) of
                              (O0 (I x), O0 (I y)) -> case op2' o2 x y of
                                                        Left () -> O1 (Con Left') (O0 Unit)
                                                        Right z -> O1 (Con Right') (O0 (I z))
                              _                    -> O2 (Dec o2) (collapse ex) (collapse ey)
    collapseAp :: forall b c. Expr vs (b -> c) -> Expr vs b -> Expr vs c
    collapseAp ef ex = case collapse ef of
                         Lambda eλ -> collapse (subVariables apply eλ)
                         _         -> collapse ef ~$ collapse ex
      where
        apply :: forall d. Indexor (b ': vs) d -> Expr vs d
        apply IZ      = collapse ex
        apply (IS ix) = V ix
    collapseIf :: Expr vs Bool -> Expr vs b -> Expr vs b -> Expr vs b
    collapseIf eb ex ey = case collapse eb of
                            O0 (B b) | b         -> collapse ex
                                     | otherwise -> collapse ey
                            _                    -> if' (collapse eb) (collapse ex) (collapse ey)

    collapseCase :: Expr vs (Either b c) -> Expr vs (b -> d) -> Expr vs (c -> d) -> Expr vs d
    collapseCase ee el er = case collapse ee of
                              O1 (Con Left') ex  -> collapse (collapseAp el ex)
                              O1 (Con Right') ex -> collapse (collapseAp er ex)
                              _                  -> case' (collapse ee) (collapse el) (collapse er)
    collapseUnfoldrN :: Expr vs Int -> Expr vs (b -> (c, b)) -> Expr vs b -> Expr vs [c]
    collapseUnfoldrN en ef ez = case collapse en of
                                O0 (I i) | i <= 0    -> nil'
                                         | otherwise -> collapse (unfold (i - 1))
                                _                    -> unfoldrN' (collapse en) (collapse ef) (collapse ez)
      where
        unfold i = (λ .-> fst' (V IZ) ~: unfoldrN' (iI i)
                                                   (undefined ef)
                                                   (snd' (V IZ))
                   ) ~$ (ef ~$ ez)
    collapseFoldr :: Expr vs (b -> c -> c) -> Expr vs c -> Expr vs [b] -> Expr vs c
    collapseFoldr ef ez exs = case collapse exs of
                                O0 Nil               -> collapse ez
                                O2 (Con Cons) ey eys -> collapse $ ef ~$ ey
                                                                      ~$ foldr' ef ez eys
                                _                    -> foldr' (collapse ef) (collapse ez) (collapse exs)

subVariables :: forall vs us a. (forall b. Indexor vs b -> Expr us b) -> Expr vs a -> Expr us a
subVariables f = runIdentity . subVariablesA (Identity . f)

subVariablesA :: forall vs us f a. Applicative f => (forall b. Indexor vs b -> f (Expr us b)) -> Expr vs a -> f (Expr us a)
subVariablesA f = go
  where
    go :: forall b. Expr vs b -> f (Expr us b)
    go e = case e of
             V ix -> f ix
             O0 o -> pure $ O0 o
             O1 o e1 -> O1 o <$> go e1
             O2 o e1 e2 -> O2 o <$> go e1 <*> go e2
             O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
             Lambda eλ -> Lambda <$> subVariablesA f' eλ
    f' :: forall b c. Indexor (c ': vs) b -> f (Expr (c ': us) b)
    f' IZ      = pure $ V IZ
    f' (IS ix) = subVariables (V . IS) <$> f ix

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

