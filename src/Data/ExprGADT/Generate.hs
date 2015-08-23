{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Data.ExprGADT.Generate where

import Control.Monad.Random
import Data.ExprGADT.Types
import Data.ExprGADT.Expr
import Control.Monad

type ExprGenerator m vs a = Int -> m (Expr vs a)

generateIf :: MonadRandom m => ExprGenerator m vs a -> ExprGenerator m vs a
generateIf gx d = if' <$> generateBool (d - 1) <*> gx (d - 1) <*> gx (d - 1)

generateInt :: MonadRandom m => ExprGenerator m vs Int
generateInt d | d <= 0    = iI <$> getRandomR (-20,20)
              | otherwise = join (fromList gens)
  where
    gens = [ (iI <$> getRandomR (-20, 29)                          , 1)
           , (abs <$> generateInt'                                 , 1)
           , (signum <$> generateInt'                              , 1)
           , (fst' <$> undefined                                   , 0)
           , (snd' <$> undefined                                   , 0)
           , ((+) <$> generateInt' <*> generateInt'                , 1)
           , ((*) <$> generateInt' <*> generateInt'                , 1)
           , ((-) <$> generateInt' <*> generateInt'                , 1)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf generateInt d                             , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateInt'  <*> undefined , 0)
           ]
    generateInt' = generateInt (d - 1)

generateBool :: MonadRandom m => ExprGenerator m vs Bool
generateBool d | d <= 0 = bB <$> getRandom
               | otherwise = join (fromList gens)
  where
    gens = [ (bB <$> getRandom                                     , 1)
           , (not' <$> generateBool'                               , 1)
           , (fst' <$> undefined                                   , 0)
           , (snd' <$> undefined                                   , 0)
           , ((~<=) <$> generateInt' <*> generateInt'              , 1)
           , ((~<) <$> generateInt' <*> generateInt'               , 1)
           , ((~==) <$> generateInt' <*> generateInt'              , 1)
           , ((~&&) <$> generateBool' <*> generateBool'            , 1)
           , ((~||) <$> generateBool' <*> generateBool'            , 1)
           , (xor' <$> generateBool' <*> generateBool'             , 1)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf generateBool d                            , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateBool' <*> undefined , 0)
           ]
    generateBool' = generateBool (d - 1)
    generateInt' = generateInt (d - 1)

-- this is kind of silly, heh
generateUnit :: MonadRandom m => ExprGenerator m vs ()
generateUnit d | d <= 0    = return unit'
               | otherwise = join (fromList gens)
  where
    gens = [ (return unit'                                         , 1)
           , (fst' <$> undefined                                   , 0)
           , (snd' <$> undefined                                   , 0)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf generateUnit d                            , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateUnit' <*> undefined , 0)
           ]
    generateUnit' = generateUnit (d - 1)

generateList :: MonadRandom m => ExprGenerator m vs a -> ExprGenerator m vs [a]
generateList gx d | d <= 0    = return nil'
                  | otherwise = join (fromList gens)
  where
    gens = [ (return nil'                                          , 0.1)
           , ((~:) <$> gx' <*> generateList'                       , 1)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf (generateList gx) d                       , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateList' <*> undefined , 0)
           , (unfoldrN' <$> generateInt (d - 1) <*> undefined <*> undefined, 0)
           , (map' <$> undefined <*> undefined, 0)
           , (mapMaybe' <$> undefined <*> undefined, 0)
           , (filter' <$> undefined <*> undefined, 0)
           ]
    gx'           = gx (d - 1)
    generateList' = generateList gx (d - 1)

-- data EType :: * -> * where
--   EInt :: EType Int
--   EBool :: EType Bool
--   EUnit :: EType ()
--   ETup :: EType a -> EType b -> EType (a, b)
--   EEither :: EType a -> EType b -> EType (Either a b)
--   EFunc :: EType a -> EType b -> EType (a -> b)
--   EList :: EType a -> EType [a]

generateETypeW :: MonadRandom m => Int -> m ETypeW
generateETypeW d | d <= 0    = join (fromList gens0)
                 | otherwise = join (fromList gens)
  where
    gens0 = [ (return (ETW EInt) , 1)
            , (return (ETW EBool), 1)
            , (return (ETW EUnit), 1)
            ]
    gens  = gens0
         ++ [ ((\(ETW t1) (ETW t2) -> ETW (ETup t1 t2)) <$> generateETypeW' <*> generateETypeW'    , 1)
            , ((\(ETW t1) (ETW t2) -> ETW (EEither t1 t2)) <$> generateETypeW' <*> generateETypeW' , 1)
            , ((\(ETW t1) (ETW t2) -> ETW (EFunc t1 t2)) <$> generateETypeW' <*> generateETypeW'   , 1)
            , ((\(ETW t) -> ETW (EList t)) <$> generateETypeW'                                     , 1)
            ]
    generateETypeW' = generateETypeW (d - 1)

-- generateExprW :: MonadRandom m => Int -> m ExprW
-- generateExprW d = do
--     etw <- generateETypeW 2
--     undefined

-- genFromEType :: MonadRandom m => EType a -> ExprGenerator m vs a
-- genFromEType EInt = generateInt
-- genFromEType EBool = generateBool
-- genFromEType EUnit = generateUnit
-- -- genFromEType (ETup a b) =


-- instance Rando (Expr '[] Int) where
--     rando 0 = iI <$> getRandomR (-10,10)
--     rando d = do
--         c <- getRandomR (0, 12 :: Int)
--         case c of
--           0 -> iI <$> getRandomR (-10, 10)
--           1 -> abs <$> rando (d - 1)
--           2 -> signum <$> rando (d - 1)
--           -- fst -- (Int, a)
--           3 -> undefined
--           -- snd -- (a, Int)
--           4 -> undefined
--           5 -> (+) <$> rando (d - 1) <*> rando (d - 1)
--           6 -> (*) <$> rando (d - 1) <*> rando (d - 1)
--           -- 7 -> div' <$> rando (d - 1) <*> rando (d - 1)
--           -- 8 -> mod' <$> rando (d - 1) <*> rando (d - 1)
--           -- ap -- (a -> Int), a
--           9 -> undefined
--           10 -> if' <$> rando (d - 1) <*> rando (d - 1) <*> rando (d - 1)
--           -- case -- Either a b, (a -> Int), (b -> Int)
--           11 -> undefined
--           -- foldr -- (a -> (Int -> Int)), [a]
--           12 -> undefined
--           _ -> undefined

-- instance Rando (Expr '[] Bool) where
--     rando 0 = bB <$> getRandom
--     rando d = do
--       c <- getRandomR (0, 13 :: Int)
--       case c of
--         0 -> bB <$> getRandom
--         1 -> not' <$> rando (d - 1)
--         -- fst -- (Bool, a)
--         2 -> undefined
--         -- snd -- (a, Bool)
--         3 -> undefined
--         4 -> (~<=) <$> rando (d - 1) <*> rando (d - 1)
--         5 -> (~<) <$> rando (d - 1) <*> rando (d - 1)
--         6 -> (~==) <$> rando (d - 1) <*> rando (d - 1)
--         7 -> (~&&) <$> rando (d - 1) <*> rando (d - 1)
--         8 -> (~||) <$> rando (d - 1) <*> rando (d - 1)
--         9 -> xor' <$> rando (d - 1) <*> rando (d - 1)
--         -- ap -- (a -> Bool), a
--         10 -> undefined
--         11 -> if' <$> rando (d - 1) <*> rando (d - 1) <*> rando (d - 1)
--         -- case -- Either a b, a -> Bool, b -> Bool
--         12 -> undefined
--         -- foldr -- (a -> (Bool -> Bool)), [a]
--         13 -> undefined
--         _ -> undefined

-- instance (Rando (Expr '[] a), Rando (Expr '[] b)) => Rando (Expr '[] (a, b)) where
--     rando 0 = tup' <$> rando 0 <*> rando 0
--     rando d = do
--       c <- getRandomR (0, 4 :: Int)
--       case c of
--         0 -> tup' <$> rando (d - 1) <*> rando (d - 1)
--         -- ap -- (a -> (b, c)), a
--         1 -> undefined
--         2 -> if' <$> rando (d - 1) <*> rando (d - 1) <*> rando (d - 1)
--         -- case -- Either a b, (a -> (c, d)), (b -> (c, d))
--         3 -> undefined
--         -- foldr -- (a -> (b, c) -> (b, c)), [a], (b, c)
--         4 -> undefined
--         _ -> undefined


-- instance (Rando (Expr '[] a), Rando (Expr '[] b)) => Rando (Expr '[] (Either a b)) where
--     rando 0 = do
--       b <- getRandom
--       if b
--         then left' <$> rando 0
--         else right' <$> rando 0
--     rando d = do
--         c <- getRandomR (0, 4 :: Int)
--         case c of
--           0 -> left' <$> rando (d - 1)
--           1 -> right' <$> rando (d - 1)
--           -- ap -- (a -> Either b c), a
--           2 -> undefined
--           3 -> if' <$> rando (d - 1) <*> rando (d - 1) <*> rando (d - 1)
--           -- case -- (a -> Either c d), (b -> Either c d)
--           4 -> undefined
--           -- foldr -- (a -> Either b c -> Either b c), [a], Either b c
--           5 -> undefined
--           _ -> undefined
