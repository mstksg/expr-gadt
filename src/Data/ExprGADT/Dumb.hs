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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Data.ExprGADT.Dumb where

import Data.ExprGADT.Dumb.Infer
import Data.ExprGADT.Dumb.Types
import Data.ExprGADT.Types
import Data.ExprGADT.Traversals
import Data.Map.Strict           (Map)
import Data.Proxy
import Data.Singletons
import Unsafe.Coerce
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

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

instance Functor (Vec n) where
    fmap _ VNil = VNil
    fmap f (x :> xs) = f x :> fmap f xs

instance Applicative (Vec NZ) where
    pure _ = VNil
    _ <*> _ = VNil

instance Applicative (Vec n) => Applicative (Vec (NS n)) where
    pure x = x :> pure x
    (f :> fx) <*> (x :> xs) = f x :> (fx <*> xs)

type family NPlus (n :: PNat) (m :: PNat) :: PNat where
    NPlus NZ m = m
    NPlus (NS n) m = NS (NPlus n m)

addSN :: forall n m nm. (NPlus n m ~ nm)
      => Sing n -> Sing m -> Sing nm
addSN SNZ y = y
addSN (SNS x) y = SNS (addSN x y)

type family NSub (n :: PNat) (m :: PNat) :: PNat where
    NSub n      NZ      = NZ
    NSub NZ     m       = m
    NSub (NS n) (NS m)  = NSub n m

subSN :: forall n m nm. (NSub n m ~ nm)
      => Sing n -> Sing m -> Sing nm
subSN _ SNZ = SNZ
subSN SNZ y = y
subSN (SNS x) (SNS y) = subSN x y

type family NComp (n :: PNat) (m :: PNat) :: Ordering where
    NComp NZ NZ = EQ
    NComp n NZ = GT
    NComp NZ m = LT
    NComp (NS n) (NS m) = NComp n m

type family NMin (n :: PNat) (m :: PNat) :: PNat where
    NMin n NZ = NZ
    NMin NZ m = NZ
    NMin (NS n) (NS m) = NS (NMin n m)

instance SingI NZ where
    sing = SNZ

instance SingI n => SingI (NS n) where
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
collapseTExpr (TEV n)  = PT (SNS SNZ) (\(t :> VNil) -> t)    -- todo
collapseTExpr (TEO0 t) = PT SNZ (\_ -> ETW t)
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

-- unDumb :: DumbExpr -> Either TypeError PolyExpr
-- unDumb e = case e of
--              -- DV v  | v <= 0    -> Right . PE (SNS SNZ) $ \(ETW x :> VNil) -> EW (x :* ENil) x (V IZ)
--                    -- | otherwise -> do
--                    --     PE n f <- unDumb $ DV (v - 1)
--                    --     let f' = undefined
--                    --     return $ PE (SNS n) f'
--              DO0 o -> case o of
--                         I _  -> Right . PE SNZ $ \_ -> EW ENil EInt (O0 o)
--                         B _  -> Right . PE SNZ $ \_ -> EW ENil EBool (O0 o)
--                         Unit -> Right . PE SNZ $ \_ -> EW ENil EUnit (O0 o)
--                         Nil  -> Right . PE (SNS SNZ) $ \(ETW x :> VNil) -> EW (x :* ENil) (EList x) (O0 Nil)
--              DO1 o e1 -> case o of
--                            Abs -> undefined

data UDEnv n where
    UDE :: Map VName (NatIxor n) -> Vec n ETypeW -> UDEnv n

data NatIxor :: PNat -> * where
    NIZ :: NatIxor (NS n)
    NIS :: NatIxor n -> NatIxor (NS n)

nameToEW :: UDEnv n -> VName -> Maybe ExprW
nameToEW (UDE mp tv) v = tVecToEW tv <$> M.lookup v mp
  where
    tVecToEW :: Vec n ETypeW -> NatIxor n -> ExprW
    tVecToEW (ETW t :> ts) i = case i of
                                 NIZ    -> EW (t :* ENil) t (V IZ)
                                 NIS i' -> case tVecToEW ts i' of
                                             EW ets _ _ -> EW (t :* ets) t (V IZ)
    tVecToEW VNil _ = error "impossible. type system should prevent.  what even"

data PolyExpr :: * where
    PE :: Sing n -> (forall t. EType t -> Maybe (VecHole n ETypeW)) -> (Vec n ETypeW -> ExprW) -> PolyExpr

data VecHole :: PNat -> * -> * where
    VH :: Sing n -> (Vec n a -> Vec m a) -> VecHole m a

unDumbWith :: UDEnv n -> DumbExpr -> Maybe PolyExpr
unDumbWith ude e =
    case e of
      DV v -> PE SNZ (const Nothing) . const <$> nameToEW ude v
      DO0 o -> case o of
                 I _ -> return . PE SNZ (const Nothing) $ \_ -> EW ENil EInt (O0 o)
                 B _ -> return . PE SNZ (const Nothing) $ \_ -> EW ENil EBool (O0 o)
                 Unit -> return . PE SNZ (const Nothing) $ \_ -> EW ENil EUnit (O0 o)
                 Nil -> return $ PE (SNS SNZ) (\case EList t -> Just $ VH SNZ (\_ -> ETW t :> VNil)
                                                     _       -> Nothing )
                                              (\(ETW t :> VNil) -> EW ENil (EList t) (O0 Nil))
      DO1 o e1 -> case o of
                    Abs    -> mkO1 EInt EInt e1   $ \case EW e1vs EInt e1e  -> Just $ EW e1vs EInt (O1 o e1e)
                                                          _                 -> Nothing
                    Signum -> mkO1 EInt EInt e1   $ \case EW e1vs EInt e1e  -> Just $ EW e1vs EInt (O1 o e1e)
                                                          _                 -> Nothing
                    Not    -> mkO1 EBool EBool e1 $ \case EW e1vs EBool e1e -> Just $ EW e1vs EBool (O1 o e1e)
                                                          _                 -> Nothing
                    Left'  -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE (SNS ts) (\case EEither t1 t2 -> do
                                                    VH hs g <- vh t1
                                                    return . VH hs $ \xs -> ETW t2 :> g xs
                                                  _             -> Nothing
                                           )
                                           (\(ETW t :> etws) -> case f etws of
                                                                  EW e1vs e1t e1e -> EW e1vs (EEither e1t t) (O1 Left' e1e)
                                           )
                    Right' -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE (SNS ts) (\case EEither t1 t2 -> do
                                                    VH hs g <- vh t2
                                                    return . VH hs $ \xs -> ETW t1 :> g xs
                                                  _             -> Nothing
                                           )
                                           (\(ETW t :> etws) -> case f etws of
                                                                  EW e1vs e1t e1e -> EW e1vs (EEither t e1t) (O1 Right' e1e)
                                           )
                    Fst -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE ts (\t1 -> do
                                       VH hs g <- vh $ ETup t1 undefined    -- crap
                                       undefined
                                     )
                                     undefined
  where
    mkO1 :: EType a -> EType b -> DumbExpr -> (ExprW -> Maybe ExprW) -> Maybe PolyExpr
    mkO1 t1 t2 e1 apply = do
      PE ts vh f <- unDumbWith ude e1
      VH ts' g <- vh t1
      return $ PE ts' (const Nothing) (\xs ->
                 let e = f (g xs)
                     err = case e of
                             EW _ t0 _ -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
                                                            , show t1
                                                            , " but got "
                                                            , show t0
                                                            ]
                 in  fromMaybe err (apply e)
               )

    -- intO1 :: Op1 Int Int -> DumbExpr -> Maybe PolyExpr
    -- intO1 o e1 = do
    --   PE ts vh f <- unDumbWith ude e1
    --   VH ts' g <- vh EInt
    --   return $ PE ts' (const Nothing) (\xs -> case f (g xs) of
    --                                             EW e1vs EInt e1e -> EW e1vs EInt (O1 o e1e)
    --                                             EW _ t _ -> error $ "Was promised an EInt by unDumbWith but got " ++ show t
    --                                   )
    --   -- case f feed of
    --   --   EW _ EInt _ -> return . PE ts c
    --   --                         $ \xs -> case f xs of
    --   --                                    EW e1vs EInt e1e -> EW e1vs EInt (O1 Abs e1e)
    --   --                                    -- EW _ _ _ ->


-- etListToExpr :: ETList (v ': vs) -> PolyExpr
-- etListToExpr (t :* ts)   = PE SNZ $ \_ -> EW (t :* ts) t (V IZ)

-- testSomeSing :: SomeSing ('KProxy :: KProxy PNat) -> String
-- testSomeSing n = case n of
--                    SomeSing SNZ -> "hey"
--                    SomeSing (SNS x) -> "yo " ++ testSomeSing (SomeSing x)

        -- (ss, PT n f) <- maybe undefined Right $ M.lookup v env
        -- undefined
        -- case n of
        --   SNZ -> case f VNil of
        --            ETW t -> makeVar ss t
          -- case ss of
          --                     NZ -> Right . PE SNZ $ \_ -> EW (t :* ENil) t (V IZ)
          --                     NS i -> do
          --                       PE n g <- unDumbWith ude


                        -- PT n f <- maybe undefined Right $ M.lookup v (udNames env)
                        -- undefined
                        -- case n of
                        --   SNZ -> case f VNil of
                        --            -- ETW t ->
                        -- -- undefined
