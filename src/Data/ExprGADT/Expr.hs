{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.ExprGADT.Expr where

-- import Data.List (uncons)

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k


data Expr :: [*] -> * -> * where
    V      :: Indexor vs a         -> Expr vs a
    O0     :: Op0 a                -> Expr vs a
    O1     :: Op1 a b              -> Expr vs a        -> Expr vs b
    O2     :: Op2 a b c            -> Expr vs a        -> Expr vs b        -> Expr vs c
    O3     :: Op3 a b c d          -> Expr vs a        -> Expr vs b        -> Expr vs c -> Expr vs d
    (:$)   :: Expr (a ': vs) b     -> Expr vs a        -> Expr vs b
    Case   :: Expr vs (Either a b) -> Expr (a ': vs) c -> Expr (b ': vs) c -> Expr vs c
    -- Const  :: Expr vs a -> Expr (v ': vs) a

infixl 1 :$

data Op0 :: * -> * where
    I :: Int -> Op0 Int
    B :: Bool -> Op0 Bool
    Nil :: Op0 [a]
    Unit :: Op0 ()

data Op1 :: * -> * -> * where
    Abs    :: Op1 Int Int
    Signum :: Op1 Int Int
    Not    :: Op1 Bool Bool
    Fst    :: Op1 (a, b) a
    Snd    :: Op1 (a, b) b
    Uncons :: Op1 [a] (Either () (a, [a]))
    Left'  :: Op1 a (Either a b)
    Right' :: Op1 b (Either a b)

data Op2 :: * -> * -> * -> * where
    Plus    :: Op2 Int Int Int
    Times   :: Op2 Int Int Int
    Minus   :: Op2 Int Int Int
    LEquals :: Op2 Int Int Bool
    And     :: Op2 Bool Bool Bool
    Or      :: Op2 Bool Bool Bool
    Cons    :: Op2 a [a] [a]
    Tup     :: Op2 a b (a, b)
    Const   :: Op2 a b a

data Op3 :: * -> * -> * -> * -> * where
    If :: Op3 Bool a a a

deriving instance Show (Indexor ks k)
deriving instance Show (Op1 a b)
deriving instance Show (Op2 a b c)
deriving instance Show (Op3 a b c d)

forbidden :: Expr vs a -> String -> b
forbidden _ r = error $ "Impossible branch! " ++ r

eval :: Expr '[] a -> a
eval e = case e of
           V _           -> forbidden e "No V constructors possible with Expr '[] a"
           O0 o          -> op0 o
           O1 o e1       -> op1 o (eval e1)
           O2 o e1 e2    -> op2 o (eval e1) (eval e2)
           O3 o e1 e2 e3 -> op3 o (eval e1) (eval e2) (eval e3)
           e1 :$ e2      -> eval $ reduceWith e2 e1
           Case ee el er -> eval $
             case ee of
               O1 Left'  ex  -> reduceWith ex el
               O1 Right' ex  -> reduceWith ex er
               O1 Uncons exs ->
                 case exs of
                   O0 Nil         -> el :$ O0 Unit
                   O2 Cons ey eys -> er :$ O2 Tup ey eys
                   _              -> forbidden e "Only constructors of [] should be O0 Nil and O2 Cons"
               _            -> forbidden e "Only constructors of Either should be Left', Right', Uncons'"

reduceWith :: Expr vs v -> Expr (v ': vs) a -> Expr vs a
reduceWith ev e = case e of
                    V IZ          -> ev
                    V (IS v)      -> V v
                    O0 o          -> O0 o
                    O1 o e1       -> O1 o (reduceWith ev e1)
                    O2 o e1 e2    -> O2 o (reduceWith ev e1) (reduceWith ev e2)
                    O3 o e1 e2 e3 -> O3 o (reduceWith ev e1) (reduceWith ev e2) (reduceWith ev e3)
                    ef :$ ex      -> reduceWith ev (reduceWith ex ef)
                    Case ee el er -> reduceWith ev $
                      case ee of
                        O1 Left' ex   -> el :$ ex
                        O1 Right' ex  -> er :$ ex
                        O1 Uncons exs ->
                          case exs of
                            O0 Nil         -> el :$ O0 Unit
                            O2 Cons ey eys -> er :$ O2 Tup ey eys
                            _              -> forbidden e "Only constructors of [] should be O0 Nil and O2 Cons"
                        _            -> forbidden e "Only constructors of Either should be Left', Right', Uncons'"
                    -- Const e1      -> e1

foldr' :: Expr ((a, b) ': vs) b -> Expr vs b -> Expr vs [a] -> Expr vs b
foldr' ef ez exs = case exs of
                     O0 Nil         -> ez
                     O2 Cons ey eys -> ef :$ O2 Tup ey (foldr' ef ez eys)
                     _              -> forbidden exs "Only constructors of [] should be O0 Nil and O2 Cons"
-- foldr' ef ez exs = Case (O1 Uncons exs) (Const ez) (_ ef :$ O2 Tup (O1 Fst (V IZ)) undefined)
-- foldr' ef ez exs = Case (O1 Uncons exs) (Const ez) (undefined ef :$ O2 Tup (O1 Fst (V IZ)) (Const ez))
-- foldr' ef ez exs = Case (O1 Uncons exs) (Const ez) (undefined ef :$ O2 Tup (O1 Fst (V IZ)) ())
-- foldr_ f z (x:xs) = f x (foldr_ f z xs)

sum' :: Expr vs [Int] -> Expr vs Int
sum' = foldr' (O2 Plus (O1 Fst (V IZ)) (O1 Snd (V IZ))) (O0 (I 0))

-- curry' :: Expr ((a, b) ': vs) c -> Expr (a ': b ': vs) c
-- curry' ef = shuffleVars _ ef :$ O2 Tup (V IZ) (V (IS IZ))
--   -- where
--   --   f = _ IS

-- pull :: Expr (a ': b ': vs) c -> Expr (a ': vs)

shuffleVars :: forall ks js c. (forall k. Indexor ks k -> Indexor js k) -> Expr ks c -> Expr js c
shuffleVars f = go
  where
    go :: forall d. Expr ks d -> Expr js d
    go e = case e of
             V ix          -> V (f ix)
             O0 o          -> O0 o
             O1 o e1       -> O1 o (go e1)
             O2 o e1 e2    -> O2 o (go e1) (go e2)
             O3 o e1 e2 e3 -> O3 o (go e1) (go e2) (go e3)
             ef :$ ex      -> go' ef :$ go ex
             Case ee el er -> Case (go ee) (go' el) (go' er)
    go' :: forall a d. Expr (a ': ks) d -> Expr (a ': js) d
    go' = shuffleVars (repushor f)

repushor :: (Indexor ks k -> Indexor js k) -> Indexor (a ': ks) k -> Indexor (a ': js) k
repushor f ix = case ix of
                  IZ     -> IZ
                  IS ix' -> IS (f ix')

op0 :: Op0 a -> a
op0 (I i) = i
op0 (B b) = b
op0 Nil   = []
op0 Unit  = ()

op1 :: Op1 a b -> a -> b
op1 Abs    = abs
op1 Signum = signum
op1 Not    = not
op1 Fst    = fst
op1 Snd    = snd
op1 Uncons = \x -> case x of
                       []     -> Left ()
                       (y:ys) -> Right (y, ys)
op1 Left'  = Left
op1 Right' = Right

op2 :: Op2 a b c -> a -> b -> c
op2 Plus    = (+)
op2 Times   = (*)
op2 Minus   = (-)
op2 LEquals = (<=)
op2 And     = (&&)
op2 Or      = (||)
op2 Cons    = (:)
op2 Tup     = (,)
op2 Const   = const

op3 :: Op3 a b c d -> a -> b -> c -> d
op3 If b x y = if b then x else y

instance Num (Expr vs Int) where
    (+)         = O2 Plus
    (*)         = O2 Times
    (-)         = O2 Minus
    abs         = O1 Abs
    signum      = O1 Signum
    fromInteger = O0 . I . fromInteger

