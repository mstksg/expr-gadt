{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Data.ExprGADT.Dumb where

import Data.ExprGADT.Dumb.Types
import Data.ExprGADT.Types
import Data.Typeable
import Data.ExprGADT.Traversals
import Control.Exception
import Data.Map.Strict           (Map)
import Data.Singletons.Decide
import Data.Proxy
import Control.Monad.Except
import Data.Singletons
import Data.Proof.EQ as Ty
import Data.IsTy
import Unsafe.Coerce
import Control.Applicative
import Data.Maybe
import qualified Data.Map.Strict as M

data PolyType :: * where
    PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

data PNat :: * where
    NZ :: PNat
    NS :: PNat -> PNat
  deriving (Eq, Ord, Show)

data instance Sing (n :: PNat) where
    SNZ :: Sing 'NZ
    SNS :: Sing (m :: PNat) -> Sing ('NS m)

deriving instance Show (Sing (n :: PNat))

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

instance Functor (Vec n) where
    fmap _ VNil = VNil
    fmap f (x :> xs) = f x :> fmap f xs

instance Applicative (Vec 'NZ) where
    pure _ = VNil
    _ <*> _ = VNil

instance Applicative (Vec n) => Applicative (Vec ('NS n)) where
    pure x = x :> pure x
    (f :> fx) <*> (x :> xs) = f x :> (fx <*> xs)

type family NPlus (n :: PNat) (m :: PNat) :: PNat where
    NPlus 'NZ m = m
    NPlus ('NS n) m = 'NS (NPlus n m)

addSN :: forall n m nm. (NPlus n m ~ nm)
      => Sing n -> Sing m -> Sing nm
addSN SNZ y = y
addSN (SNS x) y = SNS (addSN x y)

concatVec :: forall n m a. Vec n a -> Vec m a -> Vec (NPlus n m) a
concatVec VNil      y = y
concatVec (x :> xs) y = x :> concatVec xs y

type family NSub (n :: PNat) (m :: PNat) :: PNat where
    NSub n      'NZ      = 'NZ
    NSub 'NZ     m       = m
    NSub ('NS n) ('NS m)  = NSub n m

subSN :: forall n m nm. (NSub n m ~ nm)
      => Sing n -> Sing m -> Sing nm
subSN _ SNZ = SNZ
subSN SNZ y = y
subSN (SNS x) (SNS y) = subSN x y

type family NComp (n :: PNat) (m :: PNat) :: Ordering where
    NComp 'NZ 'NZ = 'EQ
    NComp n 'NZ = 'GT
    NComp 'NZ m = 'LT
    NComp ('NS n) ('NS m) = NComp n m

type family NMin (n :: PNat) (m :: PNat) :: PNat where
    NMin n 'NZ = 'NZ
    NMin 'NZ m = 'NZ
    NMin ('NS n) ('NS m) = 'NS (NMin n m)

instance SingI 'NZ where
    sing = SNZ

instance SingI n => SingI ('NS n) where
    sing = SNS sing

takeVec :: Sing n -> Vec m a -> Maybe (Vec n a)
takeVec SNZ _             = Just VNil
takeVec (SNS n) (x :> xs) = (x :>) <$> takeVec n xs
takeVec (SNS _) VNil      = Nothing

applyOnLast :: (Vec m a -> b) -> Sing n -> Vec (NPlus n m) a -> b
applyOnLast f SNZ xs = f xs
applyOnLast f (SNS i) (_ :> xs) = applyOnLast f i xs
applyOnLast _ (SNS _) _ = error "impossible...cannot be called."

collapseTExpr :: TExpr -> PolyType
collapseTExpr (TEV _)  = PT (SNS SNZ) (\(t :> VNil) -> t)    -- todo
collapseTExpr (TEO0 t) = PT SNZ (\VNil -> ETW t)
collapseTExpr (TEO1 o t1) = case collapseTExpr t1 of
                              PT n f ->
                                case o of
                                  TOList -> PT n $ \ts ->
                                              case f ts of
                                                ETW t -> ETW (EList t)
collapseTExpr (TEO2 o t1 t2) = case (collapseTExpr t1, collapseTExpr t2) of
                                 (PT (n :: Sing n) f, PT (m :: Sing m) g) ->
                                   PT (addSN n m) $ \(ts :: Vec (NPlus n m) ETypeW) ->
                                     let Just etw1 = f <$> takeVec n ts
                                         etw2 = applyOnLast g n ts
                                     in  case (etw1, etw2) of
                                           (ETW t1', ETW t2') -> case o of
                                                                   TOEither -> ETW (EEither t1' t2')
                                                                   TOTuple -> ETW (ETup t1' t2')
                                                                   TOFunc -> ETW (EFunc t1' t2')

type family CompIx (as :: [k]) (n :: PNat) :: Ordering where
    CompIx '[] 'NZ = 'EQ
    CompIx '[] x   = 'LT
    CompIx xs  'NZ = 'GT
    CompIx (x ': xs) ('NS i) = CompIx xs i

data UDEnv :: [*] -> * where
    UDE :: (CompIx vs ('NS n) ~ 'LT) => Map VName (NatIxor n) -> ETList vs -> UDEnv vs

data NatIxor :: PNat -> * where
    NIZ :: NatIxor ('NS n)
    NIS :: NatIxor n -> NatIxor ('NS n)

emptyUDE :: UDEnv '[]
emptyUDE = UDE M.empty ENil

nameToEWI :: UDEnv vs -> VName -> Maybe (ExprWIx vs)
nameToEWI (UDE mp tv) v = etlToEWI tv <$> M.lookup v mp
  where
    etlToEWI :: forall us n. (CompIx us ('NS n) ~ 'LT) => ETList us -> NatIxor n -> ExprWIx us
    etlToEWI (t :* _)  NIZ      = EWI t (V IZ)
    etlToEWI (_ :* ts) (NIS ix) = case etlToEWI ts ix of
                                    EWI t (V ixr) -> EWI t (V (IS ixr))
                                    _             -> error "i don't know what even"
    etlToEWI ENil _ = error "type system prevented this"

data PolyExpr :: [*] -> * where
    PE :: Sing n -> (PolyType -> Maybe (VecHole n ETypeW)) -> (Vec n ETypeW -> ExprWIx vs) -> PolyExpr vs

-- takes care of the "rest of the m" needed to match the type; you provide
-- the n extras.
data VecHole :: PNat -> * -> * where
    VH :: Sing n -> (Vec n a -> Vec m a) -> VecHole m a

-- data PolyType :: * where
--     PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

data DumbError = DErrMismatch ETypeW
               | DErrScope VName
               | DErrNoUnify ETypeW
               deriving (Show, Typeable)

instance Exception DumbError

polyExprNil :: PolyExpr vs -> Maybe (ExprWIx vs)
polyExprNil (PE SNZ _ f) = Just $ f VNil
polyExprNil _            = Nothing


unDumbWith :: forall vs. UDEnv vs -> DumbExpr -> Either DumbError (PolyExpr vs)
unDumbWith ude e =
    case e of
      DV v -> maybe (throwError (DErrScope v)) return
            $ PE SNZ (const Nothing) . const <$> nameToEWI ude v
      DO0 o -> case o of
                 I _  -> return $ PE SNZ (exactMatch EInt) (\_ -> EWI EInt (O0 o))
                 B _  -> return $ PE SNZ (exactMatch EBool) (\_ -> EWI EBool (O0 o))
                 Unit -> return $ PE SNZ (exactMatch EUnit) (\_ -> EWI EUnit (O0 o))
                 Nil  -> return $ PE (SNS SNZ) (\ts -> do
                                                  PT SNZ ft <- Just ts
                                                  ETW (EList t) <- Just $ ft VNil
                                                  return $ VH SNZ (\_ -> ETW t :> VNil)
                                               )
                                               (\(ETW t :> VNil) -> EWI (EList t) (O0 Nil))
      DO1 o e1 -> case o of
                    Abs    -> mkO1 o EInt EInt e1
                    Signum -> mkO1 o EInt EInt e1
                    Not    -> mkO1 o EBool EBool e1
                    Left'  -> unDumbLeft e1
                    Right' -> unDumbRight e1
                    Fst    -> unDumbFst e1
                    Snd    -> unDumbSnd e1
      DO2 o e1 e2 -> case o of
                       Plus    -> mkO2 o EInt EInt EInt e1 e2
                       Minus   -> mkO2 o EInt EInt EInt e1 e2
                       Times   -> mkO2 o EInt EInt EInt e1 e2
                       LEquals -> mkO2 o EInt EInt EBool e1 e2
                       And     -> mkO2 o EBool EBool EBool e1 e2
                       Or      -> mkO2 o EBool EBool EBool e1 e2
                       Div     -> mkO2 o EInt EInt (EEither EUnit EInt) e1 e2
                       Mod     -> mkO2 o EInt EInt (EEither EUnit EInt) e1 e2
                       Tup     -> unDumbTup e1 e2
                       Cons    -> unDumbCons e1 e2
                       Ap      -> unDumbAp e1 e2
      -- DO3 o e1 e2 e3 -> do
      --   PE ts1 vh1 f1 <- unDumbWith ude e1
      --   PE ts2 vh2 f2 <- unDumbWith ude e2
      --   PE ts3 vh3 f3 <- unDumbWith ude e3
      --   return $ case o of
      --              If -> PE (addSN ts1 (addSN ts2 ts3)) (\pt@(PT vts ft) -> do
      --                                                       undefined
      --                                                       -- VH hs1 g1 <- vh2 pt
      --                                                       -- VH hs2 g2 <- vh3 pt
      --                                                       -- return $ VH (addSN hs1 hs2)
      --                                                       --             (\etws ->
      --                                                       --                 let Just etw1 = g1 <$> takeVec hs1 etws
      --                                                       --                     etw2 = applyOnLast g2 hs1 etws
      --                                                       --                 in  concatVec etw1 etw2
      --                                                       --             )
      --                                                   )
      --                         undefined
      --              -- Case -> undefined
      --              -- UnfoldrN -> undefined
      --              -- Foldr -> undefined

  where
    exactMatch :: EType a -> PolyType -> Maybe (VecHole 'NZ ETypeW)
    exactMatch t pt = do
        PT SNZ ft <- Just pt
        ETW t' <- Just $ ft VNil
        Ty.Refl <- tyEq t t'
        return $ VH SNZ (\VNil -> VNil)
    mkO1 :: Op1 a b
         -> EType a
         -> EType b
         -> DumbExpr
         -> Either DumbError (PolyExpr vs)
    mkO1 o t1 t2 e1 = do
      PE _ vh f <- unDumbWith ude e1
      VH ts' g <- maybe (throwError (DErrNoUnify (ETW t1))) return
                $ vh (PT SNZ (\VNil -> ETW t1))
      return $ PE ts' (const Nothing) (\xs ->
                 case f (g xs) of
                   EWI t1' e1e | Just Ty.Refl <- tyEq t1 t1' -> EWI t2 (O1 o e1e)
                               | otherwise -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
                                                                , show t1
                                                                , " but got "
                                                                , show t1'
                                                                ]
               )
    mkO2 :: Op2 a b c
         -> EType a
         -> EType b
         -> EType c
         -> DumbExpr
         -> DumbExpr
         -> Either DumbError (PolyExpr vs)
    mkO2 o t1 t2 t3 e1 e2 = do
      PE _ vh1 f1 <- unDumbWith ude e1
      PE _ vh2 f2 <- unDumbWith ude e2
      VH ts1' g1 <- maybe (throwError (DErrNoUnify (ETW t1))) return
                  $ vh1 (PT SNZ (\VNil -> ETW t1))
      VH ts2' g2 <- maybe (throwError (DErrNoUnify (ETW t2))) return
                  $ vh2 (PT SNZ (\VNil -> ETW t2))
      return $ PE (addSN ts1' ts2') (const Nothing) (\xs ->
                    let Just ew1 = f1 . g1 <$> takeVec ts1' xs
                        ew2      = applyOnLast (f2 . g2) ts1' xs
                    in  case (ew1, ew2) of
                          (EWI t1' e1e, EWI t2' e2e) | Just Ty.Refl <- tyEq t1 t1'
                                                     , Just Ty.Refl <- tyEq t2 t2'
                                                     -> EWI t3 (O2 o e1e e2e)
                                                     | otherwise
                                                     -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
                                                                          , show t1 ++ " and " ++ show t2
                                                                          , " but got "
                                                                          , show t1' ++ " and " ++ show t2'
                                                                          ]
                  )
    unDumbLeft :: DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbLeft e1 = do
      PE ts vh f <- unDumbWith ude e1
      return $ PE (SNS ts) (\pt -> do
                               PT SNZ ft <- Just pt
                               ETW (EEither t1 t2) <- Just $ ft VNil        -- most likely wrong!!!!! can be poly/scheme
                               VH hs g <- vh $ PT SNZ (\VNil -> ETW t1)     -- get the inner to be the expected input
                               return $ VH hs (\xs -> ETW t2 :> g xs)
                  )
                  (\(ETW t :> etws) -> case f etws of
                                         EWI e1t e1e -> EWI (EEither e1t t) (O1 Left' e1e)
                  )
    unDumbRight :: DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbRight e1 = do
      PE ts vh f <- unDumbWith ude e1
      return $ PE (SNS ts) (\pt -> do
                               PT SNZ ft <- Just pt
                               ETW (EEither t1 t2) <- Just $ ft VNil
                               VH hs g <- vh $ PT SNZ (\VNil -> ETW t2)
                               return $ VH hs (\xs -> ETW t1 :> g xs)
                  )
                  (\(ETW t :> etws) -> case f etws of
                                         EWI e1t e1e -> EWI (EEither t e1t) (O1 Right' e1e)
                  )
    unDumbFst :: DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbFst e1 = do
      PE ts vh f <- unDumbWith ude e1
      return $ PE ts (\(PT vts ft) ->
                         vh $ PT (SNS vts) (\(ETW u :> us) ->
                           case ft us of
                             ETW t1 -> ETW (ETup t1 u)
                         )
                     )
                     (\etws -> case f etws of
                                 EWI (ETup e1t _) e1e -> EWI e1t (O1 Fst e1e)
                                 _                    -> error "unDumbWith lie"
                                     )
    unDumbSnd :: DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbSnd e1 = do
      PE ts vh f <- unDumbWith ude e1
      return $ PE ts (\(PT vts ft) ->
                         vh $ PT (SNS vts) (\(ETW u :> us) ->
                           case ft us of
                             ETW t1 -> ETW (ETup u t1)
                         )
                     )
                     (\etws -> case f etws of
                                 EWI (ETup _ e1t) e1e -> EWI e1t (O1 Snd e1e)
                                 _                    -> error "unDumbWith lie"
                     )
    unDumbTup :: DumbExpr -> DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbTup e1 e2 = do
      PE ts1 vh1 f1 <- unDumbWith ude e1
      PE ts2 vh2 f2 <- unDumbWith ude e2
      return $ PE (addSN ts1 ts2) (\pt -> do
                                    PT SNZ ft <- Just pt
                                    ETW (ETup t1 t2) <- Just $ ft VNil
                                    VH hs1 g1 <- vh1 $ PT SNZ (\VNil -> ETW t1)
                                    VH hs2 g2 <- vh2 $ PT SNZ (\VNil -> ETW t2)
                                    return $ VH (addSN hs1 hs2)
                                                (\etws -> let Just etw1 = g1 <$> takeVec hs1 etws
                                                              etw2 = applyOnLast g2 hs1 etws
                                                          in  concatVec etw1 etw2
                                                )
                                  )
                                  (\etws -> let Just ew1 = f1 <$> takeVec ts1 etws
                                                ew2      = applyOnLast f2 ts1 etws
                                            in  case (ew1, ew2) of
                                                  (EWI t1 e1e, EWI t2 e2e) ->
                                                    EWI (ETup t1 t2) (O2 Tup e1e e2e)
                                  )
    unDumbCons :: DumbExpr -> DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbCons e1 e2 = do
      PE ts1 vh1 f1 <- unDumbWith ude e1
      PE ts2 vh2 f2 <- unDumbWith ude e2
      return $ PE (addSN ts1 ts2) (\pt -> do
                                     PT SNZ ft <- Just pt
                                     ETW (EList t) <- Just $ ft VNil
                                     VH hs1 g1 <- vh1 $ PT SNZ (\VNil -> ETW t)
                                     VH hs2 g2 <- vh2 $ PT SNZ (\VNil -> ETW (EList t))
                                     return $ VH (addSN hs1 hs2)
                                                 (\etws -> let Just etw1 = g1 <$> takeVec hs1 etws
                                                               etw2 = applyOnLast g2 hs1 etws
                                                           in  concatVec etw1 etw2
                                                 )
                                  )
                                  (\etws -> let Just ew1 = f1 <$> takeVec ts1 etws
                                                ew2      = applyOnLast f2 ts1 etws
                                            in  case (ew1, ew2) of
                                                  (EWI t1 e1e, EWI (EList t1') e2e)
                                                    | Just Ty.Refl <- tyEq t1 t1'
                                                    -> EWI (EList t1) (O2 Cons e1e e2e)
                                                  _ -> error "hey, does this work?"
                                  )
    unDumbAp :: DumbExpr -> DumbExpr -> Either DumbError (PolyExpr vs)
    unDumbAp e1 e2 = do
      PE ts1 vh1 f1 <- unDumbWith ude e1
      PE ts2 vh2 f2 <- unDumbWith ude e2
      return $ PE (addSN ts1 ts2)
                  (\(PT vts ft) -> do
        -- feed g1 a vec and give the result to f1 and get something that
        -- can tell the type of PE?
        -- but how to get vec..? maybe only be happy if g1 expects SNZ?
        -- does this workkkkk????? will this ever not be SNZ?  need to do
        -- lambda before testing.
        VH SNZ g1 <- vh1 $ PT (SNS vts) (\(ETW u :> us) ->
                                             case ft us of
                                               ETW t -> ETW (EFunc u t)
                                        )
        EWI (EFunc t0 _) _ <- Just $ f1 (g1 VNil)
        VH hs2 g2 <- vh2 $ PT vts (\_ -> ETW t0)
        return $ VH hs2
                    (\etws -> let Just etw1 = g1 <$> takeVec SNZ etws
                                  etw2      = applyOnLast g2 SNZ etws
                              in  concatVec etw1 etw2
                    )
                  )
                  (\etws -> let Just ew1 = f1 <$> takeVec ts1 etws
                                ew2      = applyOnLast f2 ts1 etws
                            in  case (ew1, ew2) of
                                  (EWI (EFunc t1 t2) e1e, EWI t1' e2e)
                                    | Just Ty.Refl <- tyEq t1 t1'
                                    -> EWI t2 (O2 Ap e1e e2e)
                                  _ -> error "hey what is going on, is this possible?"
                                  -- actually, might be very possible.
                                  -- because type checking is deffered
                                  -- until here.  should be some way to
                                  -- make sure that this works no matter
                                  -- what...
                  )
