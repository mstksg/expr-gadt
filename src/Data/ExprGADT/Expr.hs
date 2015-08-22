{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.ExprGADT.Expr where

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k

data Expr :: [*] -> * -> * where
    V        :: Indexor vs a                   -> Expr vs a
    O0       :: Op0 a                          -> Expr vs a
    O1       :: O (Op1 a b)     (Op1' a b)     -> Expr vs a        -> Expr vs b
    O2       :: O (Op2 a b c)   (Op2' a b c)   -> Expr vs a        -> Expr vs b        -> Expr vs c
    O3       :: O (Op3 a b c d) (Op3' a b c d) -> Expr vs a        -> Expr vs b        -> Expr vs c -> Expr vs d
    (:$)     :: Expr (a ': vs) b               -> Expr vs a        -> Expr vs b
    Case     :: Expr vs (Either a b)           -> Expr (a ': vs) c -> Expr (b ': vs) c -> Expr vs c
    UnfoldrN :: Expr vs Int -> Expr (a ': vs) (a, b) -> Expr vs a -> Expr vs [b]
    Foldr    :: Expr (a ': b ': vs) b -> Expr vs b -> Expr vs [a] -> Expr vs b

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

data Op2 :: * -> * -> * -> * where
    Plus    :: Op2 Int Int Int
    Times   :: Op2 Int Int Int
    Minus   :: Op2 Int Int Int
    Div     :: Op2 Int Int Int
    Mod     :: Op2 Int Int Int
    LEquals :: Op2 Int Int Bool
    And     :: Op2 Bool Bool Bool
    Or      :: Op2 Bool Bool Bool
    Tup     :: Op2 a b (a, b)
    Cons    :: Op2 a [a] [a]

data Op2' :: * -> * -> * -> *

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
deriving instance Eq (Indexor ks k)
deriving instance Eq (Op0 a)
deriving instance Eq (Op1 a b)
deriving instance Eq (Op1' a b)
deriving instance Eq (Op2 a b c)
deriving instance Eq (Op2' a b c)
deriving instance Eq (Op3 a b c d)
deriving instance Eq (Op3' a b c d)

forbidden :: Expr vs a -> String -> b
forbidden e r = error $ "Impossible branch prevented by type system! " ++ show e ++ " " ++ r

type family Eval (vs :: [*]) (a :: *) :: * where
    Eval '[] x = x
    Eval (v ': vs) x = x

eval :: b ~ Eval vs a => Expr vs a -> b
eval e = case reduceAll e of
           O0 o                -> op0 o
           O1 (Con o) e1       -> op1 o (eval e1)
           O2 (Con o) e1 e2    -> op2 o (eval e1) (eval e2)
           O3 (Con o) e1 e2 e3 -> op3 o (eval e1) (eval e2) (eval e3)
           V _           -> forbidden e "No variables possible..."
                            -- after reduction, there should be no Dec
                            -- constructors if there are no variables.
           _             -> error $ unlines [ "Experienced unexpected fixed point...what happened?"
                                            , show e
                                            ]

-- reduce to only Con constructors, O0, and V...ideally.
reduceAll :: Expr vs a -> Expr vs a
reduceAll e | e == e'   = e'
            | otherwise = reduceAll e'
  where
    e' = reduceWith V e

reduce :: Expr vs a -> Expr vs a
reduce = reduceWith V

reduceWith :: forall vs us o. (forall v. Indexor vs v -> Expr us v) -> Expr vs o -> Expr us o
reduceWith f = go
  where
    go :: Expr vs a -> Expr us a
    go e = case e of
             V ix              -> f ix
             O0 o              -> O0 o
             O1 o e1           -> case o of
                                    Con o'     -> case e1 of
                                                    O0 o'' -> case op1_ o' (op0 o'') of
                                                                Just x -> O0 x
                                                                _      -> O1 o (go e1)
                                                    _      -> O1 o (go e1)
                                    Dec Fst    -> reduceFst e1
                                    Dec Snd    -> reduceSnd e1
             O2 o e1 e2        -> case o of
                                    Con o' -> case (e1, e2) of
                                                (O0 o''1, O0 o''2) -> case op2_ o' (op0 o''1) (op0 o''2) of
                                                                        Just x -> O0 x
                                                                        _      -> O2 o (go e1) (go e2)
                                                _           -> O2 o (go e1) (go e2)
                                    Dec _ -> forbidden e "There aren't even any constructors for Op2'.  How absurd."
             O3 o e1 e2 e3     -> case o of
                                    Con _  -> forbidden e "There aren't even any constructors for Op3.  How absurd."
                                    Dec If -> reduceIf e1 e2 e3
             ef :$ ex          -> reduceAp ef ex
             Case ee el er     -> reduceCase ee el er
             UnfoldrN en ef ez -> reduceUnfoldrN en ef ez
             Foldr ef ez exs   -> reduceFoldr ef ez exs
    reduceFst :: Expr vs (a, b) -> Expr us a
    reduceFst e' = case e' of
                     O2 (Con Tup) e1 _ -> go e1
                     _                 -> O1 (Dec Fst) (go e')
    reduceSnd :: Expr vs (a, b) -> Expr us b
    reduceSnd e' = case e' of
                     O2 (Con Tup) _ e2 -> go e2
                     _                 -> O1 (Dec Snd) (go e')
    reduceIf :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr us a
    reduceIf eb ex ey = case eb of
                          O0 (B b) | b         -> go ex
                                   | otherwise -> go ey
                          _                    -> O3 (Dec If) (go eb) (go ex) (go ey)
    reduceAp :: forall a b. Expr (a ': vs) b -> Expr vs a -> Expr us b
    reduceAp ef ex = go $ reduceWith apply ef
      where
        apply :: forall k. Indexor (a ': vs) k -> Expr vs k
        apply IZ      = ex
        apply (IS ix) = V ix
    reduceCase :: forall a b c. Expr vs (Either a b) -> Expr (a ': vs) c -> Expr (b ': vs) c -> Expr us c
    reduceCase ee el er = case ee of
                            O1 (Con Left') ex  -> reduceAp el ex
                            O1 (Con Right') ex -> reduceAp er ex
                            _                  -> Case (go ee) (go' el) (go' er)
    reduceUnfoldrN :: Expr vs Int -> Expr (a ': vs) (a, b) -> Expr vs a -> Expr us [b]
    reduceUnfoldrN en ef ez = case reduce en of
                                O0 (I i) | i <= 0    -> O0 Nil
                                         | otherwise -> go (unfold i)
                                _                    -> UnfoldrN (go en) (go' ef) (go ez)
      where
        unfold i = O2 (Con Cons) (O1 (Dec Snd) (V IZ))
                                 (UnfoldrN (O0 (I (i - 1)))
                                           (shuffleVars (pushDown IS) ef)
                                           (O1 (Dec Fst) (V IZ))
                                 )
                :$ (ef :$ ez)
    reduceFoldr :: Expr (a ': b ': vs) b -> Expr vs b -> Expr vs [a] -> Expr us b
    reduceFoldr ef ez exs = case reduce exs of
                              O0 Nil               -> go ez
                              O2 (Con Cons) ey eys -> go $ ef :$ shuffleVars IS ey
                                                              :$ Foldr ef ez eys
                              _                    -> Foldr (go'' ef) (go ez) (go exs)

    go' :: forall d a. Expr (d ': vs) a -> Expr (d ': us) a
    go' = reduceWith f'
      where
        f' :: forall k. Indexor (d ': vs) k  -> Expr (d ': us) k
        f' IZ      = V IZ
        f' (IS ix) = shuffleVars IS $ f ix
    go'' :: forall d e a. Expr (d ': e ': vs) a -> Expr (d ': e ': us) a
    go'' = reduceWith f''
      where
        f'' :: forall k. Indexor (d ': e ': vs) k  -> Expr (d ': e ': us) k
        f'' IZ      = V IZ
        f'' (IS IZ) = V (IS IZ)
        f'' (IS (IS ix)) = shuffleVars (IS . IS) $ f ix

uncons' :: Expr vs [a] -> Expr vs (Either () (a, [a]))
uncons' = Foldr (O1 (Con Right') (Case (V (IS IZ)) caseNil caseCons)) (O1 (Con Left') (O0 Unit))
  where
    caseNil  = O2 (Con Tup) (V (IS IZ)) (O0 Nil)
    caseCons = O2 (Con Tup) (V (IS IZ)) (O2 (Con Cons) (O1 (Dec Fst) (V IZ)) (O1 (Dec Snd) (V IZ)))

map' :: Expr (a ': vs) b -> Expr vs [a] -> Expr vs [b]
map' ef = Foldr (O2 (Con Cons) (shuffleVars (pushDown (IS . IS)) ef :$ V IZ)
                               (V (IS IZ)))
                (O0 Nil)

mapMaybe' :: Expr (a ': vs) (Either () b) -> Expr vs [a] -> Expr vs [b]
mapMaybe' ef = Foldr folder (O0 Nil)
  where
    folder = Case (shuffleVars (pushDown (IS . IS)) ef :$ V IZ)
                  (V (IS (IS IZ)))
                  (O2 (Con Cons) (V IZ) (V (IS (IS IZ))))

either' :: Expr (a ': vs) c -> Expr (b ': vs) c -> Expr vs (Either a b) -> Expr vs c
either' el er ee = Case ee el er

isRight' :: Expr vs (Either a b) -> Expr vs Bool
isRight' = either' (O0 (B False)) (O0 (B True))

filter' :: Expr (a ': vs) Bool -> Expr vs [a] -> Expr vs [a]
filter' ef = mapMaybe' $ O3 (Dec If)
                            (shuffleVars (pushDown IS) ef :$ V IZ)
                            (O1 (Con Right') (V IZ))
                            (O1 (Con Left') (O0 Unit))

sum' :: Expr vs [Int] -> Expr vs Int
sum' = Foldr (O2 (Con Plus) (V IZ) (V (IS IZ))) (O0 (I 0))

equals :: Expr vs Int -> Expr vs Int -> Expr vs Bool
equals e1 e2 = O2 (Con And) (O2 (Con LEquals) e1 e2) (O2 (Con LEquals) e2 e1)

even' :: Expr vs Int -> Expr vs Bool
even' ex = equals (O2 (Con Mod) ex (O0 (I 2))) (O0 (I 0))

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

op2 :: Op2 a b c -> a -> b -> c
op2 Plus    = (+)
op2 Times   = (*)
op2 Minus   = (-)
op2 Div     = div
op2 Mod     = mod
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
               Div     -> Just . I
               Mod     -> Just . I
               LEquals -> Just . B
               And     -> Just . B
               Or      -> Just . B
               Tup     -> const Nothing
               Cons    -> const Nothing

-- op2' :: Op2' a b c -> a -> b -> c
-- op2' = error "No constructors of Op2'.  How absurd!"
-- -- op2 Cons    = (:)
-- -- op2 Const   = const

op3 :: Op3 a b c d -> a -> b -> c -> d
op3 = error "No constructors of Op3.  How absurd!"

-- op3' :: Op3' a b c d -> a -> b -> c -> d
-- op3' If b x y = if b then x else y

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
    toExpr (x:xs) = O2 (Con Cons) (toExpr x) (toExpr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
    toExpr (x, y) = O2 (Con Tup) (toExpr x) (toExpr y)

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
    toExpr (Left x)  = O1 (Con Left') (toExpr x)
    toExpr (Right x) = O1 (Con Right') (toExpr x)

exprEq :: Expr vs a -> Expr us b -> Bool
exprEq (V IZ) (V IZ) = True
exprEq (V (IS ix1)) (V (IS ix2)) = exprEq (V ix1) (V ix2)
exprEq (O0 o1) (O0 o2) = op0Eq o1 o2
exprEq (O1 (Con o1) e1) (O1 (Con o2) e2) = op1Eq o1 o2 && exprEq e1 e2
exprEq (O1 (Dec o1) e1) (O1 (Dec o2) e2) = op1'Eq o1 o2 && exprEq e1 e2
exprEq (O2 (Con o1) e1 e1') (O2 (Con o2) e2 e2') = op2Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2'
exprEq (O2 (Dec _) e1 e1') (O2 (Dec _) e2 e2') = exprEq e1 e2 && exprEq e1' e2'
exprEq (O3 (Con _) e1 e1' e1'') (O3 (Con _) e2 e2' e2'') = exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
exprEq (O3 (Dec o1) e1 e1' e1'') (O3 (Dec o2) e2 e2' e2'') = op3'Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
exprEq (f1 :$ x1) (f2 :$ x2) = exprEq f1 f2 && exprEq x1 x2
exprEq (Case e1 l1 r1) (Case e2 l2 r2) = exprEq e1 e2 && exprEq l1 l2 && exprEq r1 r2
exprEq (UnfoldrN n1 f1 z1) (UnfoldrN n2 f2 z2) = exprEq n1 n2 && exprEq f1 f2 && exprEq z1 z2
exprEq (Foldr f1 z1 xs1) (Foldr f2 z2 xs2) = exprEq f1 f2 && exprEq z1 z2 && exprEq xs1 xs2
exprEq _ _ = False

op0Eq :: Op0 a -> Op0 b -> Bool
op0Eq (I i1) (I i2) = i1 == i2
op0Eq (B b1) (B b2) = b1 == b2
op0Eq Nil    Nil    = True
op0Eq Unit   Unit   = True
op0Eq _      _      = False

op1Eq :: Op1 a b -> Op1 c d -> Bool
op1Eq Abs Abs = True
op1Eq Signum Signum = True
op1Eq Not Not = True
op1Eq Left' Left' = True
op1Eq Right' Right' = True
op1Eq _ _ = False

op1'Eq :: Op1' a b -> Op1' c d -> Bool
op1'Eq Fst Fst = True
op1'Eq Snd Snd = True
op1'Eq _ _ = False

op2Eq :: Op2 a b c -> Op2 d e f -> Bool
op2Eq Plus Plus = True
op2Eq Times Times = True
op2Eq Minus Minus = True
op2Eq Div Div = True
op2Eq Mod Mod = True
op2Eq LEquals LEquals = True
op2Eq And And = True
op2Eq Or Or = True
op2Eq Tup Tup = True
op2Eq Cons Cons = True
op2Eq _ _ = False

op3'Eq :: Op3' a b c d -> Op3' e f g h -> Bool
op3'Eq If If = True
-- op3'Eq _ _ = False

instance Eq (Expr vs a) where
    (==) = exprEq

instance Show (Expr vs a) where
    showsPrec p e = showParen (p > 10) $ case e of
                      V ix -> showString "V "
                            . showsPrec 11 ix
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
                      -- should only parentheses when p > 1 i guess but oh well
                      ef :$ ex -> showsPrec (p + 1) ef
                                . showString " :$ "
                                . showsPrec p ex
                      Case ee el er -> showString "Case "
                                     . showsPrec 11 ee
                                     . showString " "
                                     . showsPrec 11 el
                                     . showString " "
                                     . showsPrec 11 er
                      UnfoldrN en ef ez -> showString "UnfoldrN "
                                         . showsPrec 11 en
                                         . showString " "
                                         . showsPrec 11 ef
                                         . showString " "
                                         . showsPrec 11 ez
                      Foldr ef ez exs -> showString "Foldr "
                                       . showsPrec 11 ef
                                       . showString " "
                                       . showsPrec 11 ez
                                       . showString " "
                                       . showsPrec 11 exs
