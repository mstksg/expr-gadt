{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}

module Data.ExprGADT.Parse where

import Data.ExprGADT.Types
import Data.List
import Text.Parser.Token
import Control.Monad
import Text.Parser.Char
import Text.Parser.Combinators
import Control.Applicative
import qualified Data.Map as M
import Data.Map (Map)

type Var = String
type VarBounds = [Var]

data BoundVars :: [*] -> * where
    BVNil :: BoundVars '[]
    (:?) :: (String, EType v) -> BoundVars vs -> BoundVars (v ': vs)

data ExprTW :: [*] -> * where
    ExTW :: EType a -> Expr vs a -> ExprTW vs

deriving instance Show (ExprTW vs)

infixr 5 :?

deriving instance Show (BoundVars vs)

parensIf :: TokenParsing m => Bool -> m a -> m a
parensIf True  x = parens x
parensIf False x = x

etListAt :: ETList vs -> Int -> Maybe ETypeW
etListAt ets n = do
    guard $ n >= 0
    x :* xs <- Just ets
    if n == 0
      then Just (ETW x)
      else etListAt xs (n - 1)

lookupBV :: BoundVars vs -> Var -> Maybe (ExprTW vs)
lookupBV BVNil              _ = Nothing
lookupBV ((str, et) :? bvs) v
    | v == str  = Just (ExTW et (V IZ))
    | otherwise = do
        ExTW et' (V ix) <- lookupBV bvs v
        return $ ExTW et' (V (IS ix))

bvStrings :: BoundVars vs -> [Var]
bvStrings BVNil = []
bvStrings ((v, _) :? bvs) = v : bvStrings bvs

exprVar :: (Monad m, TokenParsing m) => BoundVars vs -> m (ExprTW vs)
exprVar bvs = do
    varStr <- liftA2 (:) (lower <|> char '_') (many (alphaNum <|> oneOf "_'")) <?> "Variable name"
    case lookupBV bvs varStr of
      Just e  -> return e
      Nothing -> unexpected ("Variable `" ++ varStr ++ "` not in scope.") <?> "Variable in scope: " ++ inScopeString
  where
    inScope = bvStrings bvs
    inScopeString | null inScope = "(none)"
                  | otherwise    = '{' : intercalate ", " inScope ++ "}"

-- exprVar :: (Monad m, TokenParsing m) => ETList vs -> Int -> m (ExprTW vs)
-- exprVar ets p = parensIf (p > 10) $ do
--     _ <- string "V"
--     skipSome space
--     ix <- indexor 11
--     case makeVariable ets ix of
--       Just e  -> return e
--       Nothing -> unexpected "Index out of bounds."


-- exprVar :: (Monad m, TokenParsing m) => ETList vs -> Int -> m (ExprTW vs)
-- exprVar ets p = parensIf (p > 10) $ do
--     _ <- string "V"
--     skipSome space
--     ix <- indexor 11
--     case makeVariable ets ix of
--       Just e  -> return e
--       Nothing -> unexpected "Index out of bounds."


-- data ExprIxW :: * -> * where
--     EIW :: ETList vs -> Expr vs a -> ExprIxW a

-- data ExprW :: * where
--     EW :: ETList vs -> EType a -> Expr vs a -> ExprW

-- data ExprTW :: [*] -> * where
--     ExTW :: EType a -> Expr vs a -> ExprTW vs

-- deriving instance Show ExprW
-- deriving instance Show (ExprTW vs)

-- exprInt :: forall m vs. (MonadPlus m, TokenParsing m) => ETList vs -> m (Expr vs Int)
-- exprInt ets = exprPlus 0 <|> exprIntLit <|> exprIntVar 0
--   where
--     exprPlus :: Int -> m (Expr vs Int)
--     exprPlus p = parensIf (p > 6) $ do
--       e1 <- try $ do
--         e1 <- exprIntLit <|> exprIntVar 7
--         spaces
--         string "+"
--         return e1
--       spaces
--       e2 <- exprIntLit <|> exprIntVar 6
--       return $ e1 + e2
--     exprIntLit :: m (Expr vs Int)
--     exprIntLit = iI . fromInteger <$> integer
--     exprIntVar :: Int -> m (Expr vs Int)
--     exprIntVar p = do
--       ExTW t ev <- exprVar ets p
--       case t of
--         EInt -> pure ev
--         _    -> unexpected "Variable indexes item of wrong type."

-- exprVar :: (Monad m, TokenParsing m) => ETList vs -> Int -> m (ExprTW vs)
-- exprVar ets p = parensIf (p > 10) $ do
--     _ <- string "V"
--     skipSome space
--     ix <- indexor 11
--     case makeVariable ets ix of
--       Just e  -> return e
--       Nothing -> unexpected "Index out of bounds."

-- indexor :: (Monad m, TokenParsing m, CharParsing m) => Int -> m Int
-- indexor p = iz <|> parensIf (p > 10) is
--   where
--     iz = 1 <$ string "IZ"
--     is = do
--       _ <- string "IS"
--       skipSome space
--       fmap succ $ iz <|> parens is

-- -- iwSucc :: IndexorW -> IndexorW
-- -- iwSucc (IxW ix) = IxW (IS ix)

-- fetchType :: ETList vs -> Int -> Maybe ETypeW
-- fetchType (x :* _)  0         = Just $ ETW x
-- fetchType (_ :* xs) n | n > 0 = fetchType xs (n - 1)
-- fetchType _         _         = Nothing

-- makeVariable :: ETList vs -> Int -> Maybe (ExprTW vs)
-- makeVariable ets n = do
--     guard $ n > 0
--     x :* xs <- Just ets
--     if n == 1
--       then Just $ ExTW x (V IZ)
--       else do
--         ExTW x' (V ix) <- makeVariable xs (n - 1)
--         return $ ExTW x' (V (IS ix))
