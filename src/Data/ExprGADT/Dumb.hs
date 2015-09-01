{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Dumb where

-- import Data.ExprGADT.Traversals
-- import Data.List
-- import Data.Map.Strict           (Map)
-- import Data.Proxy
-- import GHC.TypeLits
-- import qualified Data.Map.Strict
import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Data.ExprGADT.Types
import Data.Maybe
import Data.Singletons

data PNat = NZ | NS PNat

data instance Sing (a :: PNat) where
    SNZ :: Sing 'NZ
    SNS :: Sing (a :: PNat) -> Sing ('NS a)

data IxNat :: PNat -> * where
    INZ :: IxNat n
    INS :: IxNat n -> IxNat ('NS n)

data TExpr :: PNat -> * where
    TEV :: IxNat ('NS n) -> TExpr n
    TEO0 :: EType a -> TExpr n
    TEO1 :: TOp1 -> TExpr n -> TExpr n
    TEO2 :: TOp2 -> TExpr n -> TExpr n -> TExpr n
    TEScheme :: TExpr ('NS n) -> TExpr n

data TExprW :: * where
    TEW :: Sing n -> TExpr n -> TExprW

data TOp1 :: * where
    TOList :: TOp1

data TOp2 :: * where
    TOFunc :: TOp2
    TOEither :: TOp2
    TOTuple :: TOp2

type Var = Int

data DumbExpr :: * where
    DV      :: Maybe (TExpr 'NZ) -> Var         -> DumbExpr
    DO0     :: Maybe (TExpr 'NZ) -> Op0 a       -> DumbExpr
    DO1     :: Maybe (TExpr 'NZ) -> Op1 a b     -> DumbExpr -> DumbExpr
    DO2     :: Maybe (TExpr 'NZ) -> Op2 a b c   -> DumbExpr -> DumbExpr -> DumbExpr
    DO3     :: Maybe (TExpr 'NZ) -> Op3 a b c d -> DumbExpr -> DumbExpr -> DumbExpr -> DumbExpr
    DLambda :: Maybe (TExpr 'NZ) -> Var         -> DumbExpr -> DumbExpr

dumbExprT :: DumbExpr -> Maybe (TExpr 'NZ)
dumbExprT (DV t _) = t
dumbExprT (DO0 t _) = t
dumbExprT (DO1 t _ _) = t
dumbExprT (DO2 t _ _ _) = t
dumbExprT (DO3 t _ _ _ _) = t
dumbExprT (DLambda t _ _) = t

data TypeError :: * where
    TErrUnbound :: Int -> TypeError
    TErrMismatch :: TExpr n -> TExpr m -> TypeError
    TErrUnexpected :: String -> TypeError

deriving instance Show DumbExpr
deriving instance Show TypeError
deriving instance Show (IxNat n)
deriving instance Show (TExpr n)
deriving instance Show TOp1
deriving instance Show TOp2
deriving instance Show TExprW
deriving instance Show (Sing (n :: PNat))

type Env = [TExpr 'NZ]

fillInTypes :: (MonadError TypeError m, MonadReader Env m) => DumbExpr -> m DumbExpr
fillInTypes e =
    case e of
      DO0 t0 o -> return $ case o of
                    I _ -> DO0 (Just (TEO0 EInt)) o
                    B _ -> DO0 (Just (TEO0 EBool)) o
                    Unit -> DO0 (Just (TEO0 EUnit)) o
                    Nil -> DO0 (t0 <|> Just (TEScheme (TEO1 TOList (TEV INZ)))) o
      DO1 t0 o e1 -> case o of
                       Abs -> do
                         e1' <- fillInTypes e
                         case dumbExprT e1' of
                           Just (TEO0 EInt) -> return $ DO1 (Just (TEO0 EInt)) o e1'
                           Just t -> throwError $ TErrMismatch (TEO0 EInt) t
                           Nothing -> throwError $ TErrUnexpected "Unexpected non-Just from fillInTypes..."



-- infer :: (MonadError TypeError m, MonadReader Env m) => DumbExpr -> m (TExpr 'NZ)
-- infer e = case e of
--             DV i -> do
--               l <- asks $ \ts -> listToMaybe $ drop i ts
--               maybe (throwError (TErrUnbound i)) return l
--             DO0 o -> return $ case o of
--                        I _ -> TEO0 EInt
--                        B _ -> TEO0 EBool
--                        Unit -> TEO0 EUnit
--                        Nil -> TEScheme (TEO1 TOList (TEV INZ))
--                        -- Nil -> TEW (SNS SNZ) (TEO1 TOList (TEV INZ))
--             DO1 o e1 -> case o of
--                           Abs -> do
--                             t <- infer e1
--                             undefined

mkInt :: TExpr 'NZ -> Maybe (TExpr 'NZ)
mkInt te = case te of
             TEO0 EInt -> Just te
             TEScheme (TEV INZ) -> undefined
             -- how do toher things do this?
             _   -> Nothing
    -- TEScheme :: TExpr ('NS n) -> TExpr n
             -- TEO0 _ -> Nothing



-- type Env = [Scheme]

-- data TypeExpr :: * where
--     TEVar :: Int -> TypeExpr
--     TEConcrete :: EType a -> TypeExpr
--     TEO1 :: TOp1 -> TypeExpr -> TypeExpr
--     TEO2 :: TOp2 -> TypeExpr -> TypeExpr -> TypeExpr

-- data TypeError :: * where
--     TErrUnbound :: Int -> TypeError

-- data Scheme :: * where
--     ConcScheme :: TypeExpr -> Scheme
--     Forall :: Scheme -> Scheme

-- infer :: (MonadReader Env m) => DumbExpr -> m TypeExpr
-- infer e = case e of

--             DO0 o -> case o of
--                        I _ -> return $ TEConcrete EInt
--                        B _ -> return $ TEConcrete EBool
--                        Unit -> return $ TEConcrete EUnit
--                        Nil -> return $ TEO1 TOList (TEVar 0)

-- lookupEnv :: (MonadReader Env m, MonadError TypeError m)
--           => Int
--           -> m TypeExpr
-- lookupEnv x = do
--     env <- ask
--     case listToMaybe (drop x env) of
--       Nothing -> throwError $ TErrUnbound x
--       Just t  -> undefined

-- -- data PNat = NZ | NS PNat

-- -- data instance Sing (a :: PNat) where
-- --     SNZ :: Sing 'NZ
-- --     SNS :: Sing (a :: PNat) -> Sing ('NS a)

-- -- type family CompPN (x :: PNat) (y :: PNat) :: Ordering where
-- --     CompPN 'NZ 'NZ = 'EQ
-- --     CompPN 'NZ ('NS m) = 'LT
-- --     CompPN ('NS n) 'NZ = 'GT
-- --     CompPN ('NS n) ('NS m) = CompPN n m

-- -- predPN :: Sing (NS n) -> Sing n
-- -- predPN (SNS ix) = ix

-- -- -- type family Pred (x :: PNat) where
-- -- --     Pred NZ = NZ
-- -- --     Pred (NS ix) = ix

-- -- data PolyExpr :: * where
-- --     PE :: (Unfoldable (Vec n), CompPN ('NS m) n ~ 'GT)
-- --        => Sing n
-- --        -> Sing m
-- --        -> (ETypeW -> Maybe ETypeW)
-- --        -> (Vec n ETypeW -> ExprW)
-- --        -> PolyExpr

-- -- data Vec :: PNat -> * -> * where
-- --     VNil :: Vec 'NZ a
-- --     (:>) :: a -> Vec n a -> Vec ('NS n) a

-- -- infixr 5 :>

-- -- deriving instance Show e => Show (Vec n e)
-- -- deriving instance Show (Sing (n :: PNat))

-- -- class Unfoldable v where
-- --     unfold :: (a -> (b, a)) -> a -> v b

-- -- instance Unfoldable (Vec 'NZ) where
-- --     unfold _ _ = VNil

-- -- instance Unfoldable (Vec n) => Unfoldable (Vec ('NS n)) where
-- --     unfold f z = let (x, z') = f z
-- --                  in  x :> unfold f z'

-- -- replicateU :: Unfoldable v => a -> v a
-- -- replicateU = unfold (\y -> (y, y))

-- -- fromListV' :: Unfoldable v => a -> [a] -> v a
-- -- fromListV' d = unfold $ \xs -> case xs of
-- --                                  [] -> (d, [])
-- --                                  y:ys -> (y, ys)

-- -- fromListV :: Unfoldable v => [a] -> v a
-- -- fromListV = fromListV' (error "list too short")

-- -- tailV :: Vec ('NS n) a -> Vec n a
-- -- tailV (_ :> xs) = xs

-- -- indexVec :: (CompPN m n ~ 'GT) => Vec m a -> Sing n -> a
-- -- indexVec (x :> _ ) SNZ      = x
-- -- indexVec (_ :> xs) (SNS ix) = indexVec xs ix
-- -- indexVec _ _                = undefined

-- -- replaceAt :: (CompPN (NS m) n ~ 'GT) => Vec m a -> Sing n -> a -> Vec m a
-- -- replaceAt VNil SNZ x = VNil
-- -- replaceAt (x :> xs) SNZ y = x :> xs
-- -- replaceAt (x :> xs) (SNS ix) y = y :> replaceAt xs ix y

-- -- insertAt :: (CompPN (NS m) n ~ 'GT) => Vec m a -> Sing n -> a -> Vec (NS m) a
-- -- insertAt xs SNZ y = y :> xs
-- -- insertAt (x :> xs) (SNS ix) y = x :> insertAt xs ix y


-- -- vToList :: Vec n a -> [a]
-- -- vToList VNil = []
-- -- vToList (x :> xs) = x : vToList xs

-- -- zipLV :: (a -> b -> c) -> [a] -> Vec n b -> Vec n c
-- -- zipLV f = zipLV' f (error "list too short")

-- -- zipLV' :: (a -> b -> c) -> a -> [a] -> Vec n b -> Vec n c
-- -- zipLV' _ _ _ VNil = VNil
-- -- zipLV' f d [] (y :> ys) = f d y :> zipLV' f d [] ys
-- -- zipLV' f d (x:xs) (y :> ys) = f x y :> zipLV' f d xs ys

-- -- -- testUnDumb :: String
-- -- -- testUnDumb = case unDumb (DV 1) of
-- -- --                -- PE p f -> show $ f (ETW EInt :> VNil)
-- -- --                PE _ f -> show $ f (replicateU (ETW EInt))



-- -- -- infer :: ETList vs -> DumbExpr -> (ETList vs, ETypeW)


-- -- -- unDumb :: DumbExpr -> [PolyExpr]
-- -- -- unDumb e =
-- -- --     case e of
-- -- --       DV v -> case compare v 0 of
-- -- --                 LT -> empty
-- -- --                 EQ -> return . PE (SNS SNZ) (SNS SNZ) Just
-- -- --                              $ \ts -> case indexVec ts SNZ of
-- -- --                                         ETW t -> EW (t :* ENil) t (V IZ)
-- -- --                 GT -> do
-- -- --                   PE p i x f <- unDumb (DV (v - 1))
-- -- --                   let p' = SNS p
-- -- --                       i' = SNS i
-- -- --                       x' = Just
-- -- --                       f' (ETW t :> ts) = case f ts of
-- -- --                                            EW ts' t' e' -> EW (t :* ts') t' (overIxors IS e')
-- -- --                   return $ PE p' i' x' f'
-- -- --       DO0 o -> return $ case o of
-- -- --                           I _ -> PE SNZ SNZ Just $ \_ -> EW ENil EInt (O0 o)
-- -- --                           B _ -> PE SNZ SNZ Just $ \_ -> EW ENil EBool (O0 o)
-- -- --                           Unit -> PE SNZ SNZ Just $ \_ -> EW ENil EUnit (O0 o)
-- -- --                           Nil -> PE (SNS SNZ) (SNS SNZ) (\case ETW (EList t) -> Just (ETW t); _ -> Nothing)
-- -- --                                   $ \ts -> case indexVec ts SNZ of
-- -- --                                              ETW t -> EW ENil (EList t) (O0 Nil)
-- -- --       DO1 o e1 ->
-- -- --         case o of
-- -- --           Abs -> do
-- -- --             PE p i x f <- unDumb e1
-- -- --             case i of
-- -- --               SNZ ->
-- -- --                 case f (replicateU (ETW EUnit)) of
-- -- --                   EW vs EInt e' -> return . PE p i x
-- -- --                                           $ \ts -> case f ts of
-- -- --                                                      EW vs' EInt e' -> EW vs' EInt (O1 Abs e')
-- -- --                                                      EW {} -> error "Impossible!"
-- -- --                   _ -> empty
-- -- --               SNS i' ->
-- -- --                 case x (ETW EInt) of

-- --       --         SNS i' ->
-- --       --           case p of
-- --       --             SNS p' ->
-- --       --               case x (ETW EInt) of
-- --       --                 Nothing -> empty
-- --       --                 Just t ->
-- --       --                   case f (replicateU t) of
-- --       --                     EW vs EInt e' -> return . PE p' SNZ Just
-- --       --                                             $ \ts -> case f (insertAt ts i t) of
-- --       --                                                        EW vs' EInt e' -> EW vs' EInt (O1 Abs e')

-- --                         -- case f (replaceAt (replicateU (ETW EUnit)) i (ETW (x (ETW EInt)))) of
-- --                         --            _ -> empty
-- --                       --   SNS i' -> undefined
-- --                       -- let p' = 
-- --                       -- case f (replicateU (ETW EUnit)) of
-- --                       --   EW vs EInt e' -> return . PE p $ \ts -> case f ts of
-- --                       --                                             EW vs' EInt e' -> EW vs' EInt (O1 Abs e')
-- --                                                                   -- maybe
-- --                                                                   -- PolyExpr
-- --                                                                   -- can
-- --                                                                   -- fail
-- --                                                                   -- too?

-- -- -- makeMatch :: (ETypeW -> ETypeW) -> ETypeW -> ETypeW
-- -- -- makeMatch f t = undefined
-- -- --   where
-- -- --     ETW y = f t
