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

-- import Debug.Trace
-- import Control.Arrow ((|||))
-- import Data.List (uncons)
-- import Data.Void

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k

data Expr :: [*] -> * -> * where
    V      :: Indexor vs a                   -> Expr vs a
    O0     :: Op0 a                          -> Expr vs a
    O1     :: O (Op1 a b) (Op1' a b)         -> Expr vs a        -> Expr vs b
    O2     :: O (Op2 a b c) (Op2' a b c)     -> Expr vs a        -> Expr vs b        -> Expr vs c
    O3     :: O (Op3 a b c d) (Op3' a b c d) -> Expr vs a        -> Expr vs b        -> Expr vs c -> Expr vs d
    (:$)   :: Expr (a ': vs) b               -> Expr vs a        -> Expr vs b
    Case   :: Expr vs (Either a b)           -> Expr (a ': vs) c -> Expr (b ': vs) c -> Expr vs c

infixl 1 :$

data O :: * -> * -> * where
    Con :: a -> O a b
    Dec :: b -> O a b
  deriving Show

data Op0 :: * -> * where
    I :: Int -> Op0 Int
    B :: Bool -> Op0 Bool
    Nil :: Op0 [a]
    Unit :: Op0 ()

data Op1 :: * -> * -> * where
    Abs    :: Op1 Int Int
    Signum :: Op1 Int Int
    Not    :: Op1 Bool Bool
    Left'  :: Op1 a (Either a b)
    Right' :: Op1 b (Either a b)

data Op1' :: * -> * -> * where
    Fst    :: Op1' (a, b) a
    Snd    :: Op1' (a, b) b
    Uncons :: Op1' [a] (Either () (a, [a]))

data Op2 :: * -> * -> * -> * where
    Plus    :: Op2 Int Int Int
    Times   :: Op2 Int Int Int
    Minus   :: Op2 Int Int Int
    LEquals :: Op2 Int Int Bool
    And     :: Op2 Bool Bool Bool
    Or      :: Op2 Bool Bool Bool
    Tup     :: Op2 a b (a, b)

data Op2' :: * -> * -> * -> * where
    Cons    :: Op2' a [a] [a]

data Op3 :: * -> * -> * -> * -> *

data Op3' :: * -> * -> * -> * -> * where
    If :: Op3' Bool a a a

deriving instance Show (Indexor ks k)
deriving instance Show (Op0 a)
deriving instance Show (Op1 a b)
deriving instance Show (Op1' a b)
deriving instance Show (Op2 a b c)
deriving instance Show (Op2' a b c)
deriving instance Show (Op3 a b c d)
deriving instance Show (Op3' a b c d)

forbidden :: Expr vs a -> String -> b
forbidden e r = error $ "Impossible branch prevented by type system! " ++ show e ++ " " ++ r

eval :: Expr '[] a -> a
eval e = case e of
           O0 o          -> op0 o
           O1 o e1       -> onO op1 op1' o (eval e1)
           O2 o e1 e2    -> onO op2 op2' o (eval e1) (eval e2)
           O3 o e1 e2 e3 -> onO op3 op3' o (eval e1) (eval e2) (eval e3)
           V _           -> forbidden e "No variables allowed..."
           _             -> eval $ reduce e
  where
    onO f _ (Con o) = f o
    onO _ g (Dec o) = g o

reduce :: Expr vs a -> Expr vs a
reduce = reduceWith V

reduceWith :: forall vs us o. (forall v. Indexor vs v -> Expr us v) -> Expr vs o -> Expr us o
reduceWith f = go
  where
    go :: Expr vs a -> Expr us a
    go e = case e of
             V ix          -> f ix
             O0 o          -> O0 o
             O1 o e1       -> case o of
                                Con _      -> O1 o (go e1)
                                Dec Fst    -> reduceFst e1
                                Dec Snd    -> reduceSnd e1
                                Dec Uncons -> reduceUncons e1
             O2 o e1 e2    -> case o of
                                Con _    -> O2 o (go e1) (go e2)
                                Dec Cons -> reduceCons e1 e2
             O3 o e1 e2 e3 -> case o of
                                Con _  -> forbidden e "There aren't even any constructors for Op3.  How absurd."
                                Dec If -> reduceIf e1 e2 e3
             ef :$ ex      -> reduceAp ef ex
             Case ee el er -> reduceCase ee el er
    reduceFst :: Expr vs (a, b) -> Expr us a
    reduceFst e' = case e' of
                     V _               -> O1 (Dec Fst) (go e')
                     O2 (Con Tup) e1 _ -> go e1
                     _                 -> reduceFst $ reduce e'
    reduceSnd :: Expr vs (a, b) -> Expr us b
    reduceSnd e' = case e' of
                     V _               -> O1 (Dec Snd) (go e')
                     O2 (Con Tup) _ e2 -> go e2
                     _                 -> reduceSnd $ reduce e'
    reduceUncons :: Expr vs [a] -> Expr us (Either () (a, [a]))
    reduceUncons e' = case e' of
                        V _                  -> O1 (Dec Uncons) (go e')
                        O0 Nil               -> O1 (Con Left') (O0 Unit)
                        O2 (Dec Cons) ex exs -> O1 (Con Right') (O2 (Con Tup) (go ex) (go exs))
                        _                    -> reduceUncons $ reduce e'
    reduceCons :: Expr vs a -> Expr vs [a] -> Expr us [a]
    reduceCons ex exs = case exs of
                          V _                  -> O2 (Dec Cons) ex' (go exs)
                          O0 Nil               -> O2 (Dec Cons) ex' (O0 Nil)
                          O2 (Dec Cons) ey eys -> O2 (Dec Cons) ex' (O2 (Dec Cons) (go ey) (go eys))
                          _                    -> reduceCons ex (reduce exs)
      where
        ex' = go ex
    reduceIf :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr us a
    reduceIf eb ex ey = case eb of
                          V _                  -> O3 (Dec If) (go eb) (go ex) (go ey)
                          O0 (B b) | b         -> go ex
                                   | otherwise -> go ey
                          _                    -> reduceIf (reduce eb) ex ey
    reduceAp :: forall a b. Expr (a ': vs) b -> Expr vs a -> Expr us b
    reduceAp ef ex = go $ reduceWith apply ef
      where
        apply :: forall k. Indexor (a ': vs) k -> Expr vs k
        apply IZ      = ex
        apply (IS ix) = V ix
    reduceCase :: forall a b c. Expr vs (Either a b) -> Expr (a ': vs) c -> Expr (b ': vs) c -> Expr us c
    reduceCase ee el er = case ee of
                            V _                -> Case (go ee) (reduceWith f' el) (reduceWith f' er)
                            O1 (Con Left') ex  -> reduceAp el ex
                            O1 (Con Right') ex -> reduceAp er ex
                            _                  -> reduceCase (reduce ee) el er
      where
        f' :: forall k d. Indexor (d ': vs) k  -> Expr (d ': us) k
        f' IZ      = V IZ
        f' (IS ix) = shuffleVars IS $ f ix

foldr' :: forall a b vs. Expr ((a, b) ': vs) b -> Expr vs b -> Expr vs [a] -> Expr vs b
foldr' ef ez exs = case exs' of
                     O0 Nil -> ez
                     O2 (Dec Cons) ey eys -> ef :$ O2 (Con Tup) ey (foldr' ef ez eys)
                     -- loops forever
                     _ -> Case (O1 (Dec Uncons) exs')
                               ez'
                               (ef' :$ O2 (Con Tup) (O1 (Dec Fst) (V IZ)) (foldr' ef' ez' (O1 (Dec Snd) (V IZ))))
  where
    exs' = reduce exs
    ef' = shuffleVars (pushDown IS) (reduce ef)
    ez' :: forall j. Expr (j ': vs) b
    ez' = shuffleVars IS (reduce ez)

-- foldr' ef ez exs = Case (O1 (Dec Uncons) exs)
--                         ez'
--                         (ef' :$ O2 (Con Tup) (O1 (Dec Fst) (V IZ)) (foldr' ef' ez' (O1 (Dec Snd) (V IZ))))
--                         -- (ef' :$ O2 (Con Tup) (O1 (Dec Fst) (V IZ)) ez')
--   where
--     ef' = shuffleVars (pushDown IS) ef
--     ez' :: forall j. Expr (j ': vs) b
--     ez' = shuffleVars IS ez

-- sum' :: Expr vs [Int] -> Expr vs Int
-- sum' = foldr' (O2 Plus (O1 Fst (V IZ)) (O1 Snd (V IZ))) (O0 (I 0))

curry' :: Expr ((a, b) ': vs) c -> Expr (a ': b ': vs) c
curry' ef = shuffleVars f ef :$ O2 (Con Tup) (V IZ) (V (IS IZ))
  where
    f = pushDown (IS . IS)

uncurry' :: Expr (a ': b ': vs) c -> Expr ((a, b) ': vs) c
uncurry' ef = shuffleVars f ef :$ O1 (Dec Fst) (V (IS IZ)) :$ O1 (Dec Snd) (V IZ)
  where
    f = pushDown (pushDown IS)

shuffleVars :: forall ks js c. (forall k. Indexor ks k -> Indexor js k) -> Expr ks c -> Expr js c
shuffleVars f = reduceWith (V . f)

pushDown :: (Indexor ks k -> Indexor js k) -> Indexor (a ': ks) k -> Indexor (a ': js) k
pushDown f ix = case ix of
                  IZ     -> IZ
                  IS ix' -> IS (f ix')

-- coerceIndexor :: Indexor ks k -> Indexor js j
-- coerceIndexor IZ = IZ
-- coerceIndexor (IS ix) = IS (coerceIndexor ix)

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

op1' :: Op1' a b -> a -> b
op1' Fst    = fst
op1' Snd    = snd
op1' Uncons = \x -> case x of
                      []     -> Left ()
                      (y:ys) -> Right (y, ys)

op2 :: Op2 a b c -> a -> b -> c
op2 Plus    = (+)
op2 Times   = (*)
op2 Minus   = (-)
op2 LEquals = (<=)
op2 And     = (&&)
op2 Or      = (||)
op2 Tup     = (,)

op2' :: Op2' a b c -> a -> b -> c
op2' Cons = (:)
-- op2 Cons    = (:)
-- op2 Const   = const

op3 :: Op3 a b c d -> a -> b -> c -> d
op3 = error "No constructors of Op3.  How absurd!"

op3' :: Op3' a b c d -> a -> b -> c -> d
op3' If b x y = if b then x else y

instance Num (Expr vs Int) where
    (+)         = O2 (Con Plus)
    (*)         = O2 (Con Times)
    (-)         = O2 (Con Minus)
    abs         = O1 (Con Abs)
    signum      = O1 (Con Signum)
    fromInteger = O0 . I . fromInteger

class ToExpr a where
    toExpr :: a -> Expr vs a

instance ToExpr Int where
    toExpr = O0 . I

instance ToExpr Bool where
    toExpr = O0 . B

instance ToExpr () where
    toExpr _ = O0 Unit

instance ToExpr a => ToExpr [a] where
    toExpr []     = O0 Nil
    toExpr (x:xs) = O2 (Dec Cons) (toExpr x) (toExpr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
    toExpr (x, y) = O2 (Con Tup) (toExpr x) (toExpr y)

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
    toExpr (Left x)  = O1 (Con Left') (toExpr x)
    toExpr (Right x) = O1 (Con Right') (toExpr x)

instance Show (Expr vs a) where
    showsPrec p e = showParen (p > 10) $ case e of
                      V IZ -> showString "V IZ"
                      V ix -> showString "V "
                            . showParen True (shows ix)
                      O0 o -> showString "O0 "
                            . showsPrec 11 o
                      O1 o e1 -> showString "O1 "
                               . showsPrec 11 o
                               . showString " "
                               . showsPrec 11 e1
                      O2 o e1 e2 -> showString "O2 "
                                  . showsPrec 11 o
                                  . showString " "
                                  . showsPrec 11 e1
                                  . showString " "
                                  . showsPrec 11 e2
                      O3 o e1 e2 e3 -> showString "O3 "
                                     . showsPrec 11 o
                                     . showString " "
                                     . showsPrec 11 e1
                                     . showString " "
                                     . showsPrec 11 e2
                                     . showString " "
                                     . showsPrec 11 e3
                      ef :$ ex -> showsPrec (p + 1) ef
                                . showString " :$ "
                                . showsPrec p ex
                      Case ee el er -> showString "Case "
                                     . showsPrec 11 ee
                                     . showString " "
                                     . showsPrec 11 el
                                     . showString " "
                                     . showsPrec 11 er
