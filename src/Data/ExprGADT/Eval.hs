{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Data.ExprGADT.Eval where

import Control.Applicative
import Data.Bifunctor
import Data.ExprGADT.Traversals
import Data.ExprGADT.Types
import Data.Functor.Identity
import Data.List                   (unfoldr)
import Data.Type.Combinator hiding (I)
import qualified Data.Type.Combinator as C (I)
import Data.Type.HList
import Data.Type.Product
import Type.Class.HFunctor
import Type.Family.List            as L
import Data.Type.Vector
import Data.Type.Fin
import Type.Family.Nat

forbidden :: Expr vs a -> String -> b
-- forbidden e r = error $ "Impossible branch prevented by type system! " ++ show e ++ " " ++ r
forbidden _ r = error $ "Impossible branch prevented by type system! " ++ r

eval :: Expr '[] a -> a
eval = evalWith Ø

evalP :: ExprP '[] a -> a
evalP = evalWithP Ø


evalWith :: forall vs a. HList vs -> Expr vs a -> a
evalWith vs = go
  where
    go :: forall b. Expr vs b -> b
    go e = case e of
             V ix                -> subIndexor vs ix
             O o es              -> op o (map' (Identity . go) es)
             Lambda ef           -> \x -> evalWith (x :<- vs) ef

evalWith' :: forall vs a.
             (forall b. Indexor vs b -> b)
          -> Expr vs a -> a
evalWith' f = go
  where
    go :: forall b. Expr vs b -> b
    go e = case e of
             V ix      -> f ix
             O o es    -> op o (map' (Identity . go) es)
             Lambda ef -> \x -> evalWith' (f' x) ef
    f' :: forall b v. v -> Indexor (v ': vs) b -> b
    f' x IZ      = x
    f' _ (IS ix) = f ix

subIndexor :: HList ks -> (forall v. Indexor ks v -> v)
subIndexor (x :< _ ) IZ      = runIdentity x
subIndexor (_ :< xs) (IS ix) = subIndexor xs ix
subIndexor Ø      _       = error "Impossible...should be prevented by the type system. There is no Indexor '[] a."

-- maybe can do the same trick with Either to get rid of EStar?
evalWithP :: forall vs a. HList vs -> ExprP vs a -> a
evalWithP vs = go
  where
    go :: forall b. ExprP vs b -> b
    go e = case e of
             VP ix        -> subIndexor vs ix
             TP o ts      -> tOp o $ map' (go . getComp) ts
             OP o _ es    -> op o $ map' (Identity . go) es
             LambdaP _ eλ -> \x -> evalWithP (x :<- vs) eλ

-- fromExprP :: forall vs a. ExprP vs a -> Either ETypeW (Expr vs a)
-- fromExprP = go
--   where
--     go :: forall us b. ExprP us b -> Either ETypeW (Expr us b)
--     go e = case e of
--              VP ix    -> Right (V ix)
--              -- oops this is now unwritable
--              -- okay let's calm down.  the result of traverse' go ts is
--              -- a Prod of Expr vs (EType a)'s.  And the only thing those
--              -- can be are V's...or whatever the result of this function
--              -- is.  Maybe the Left term should be ETypeW's, and this could
--              -- be aggregating ETypeW's.  ANd if it's Right, it's because
--              -- it's variables, and...?
--              -- ah well there's the problem, ain't it?
--              -- hm, will anything go badly if this is just...undefined?
--              -- well, it would be nice to have a good Left.  maybe see if
--              -- they are all Left's, and if so, use tOp.  and if one is
--              -- a variable, then...?  that's the problem huh?  a variable,
--              -- or a lambda?  but maybe the lambda case should be taken
--              -- care of in the lambda branch to auto-compress it.  Hm.  Oh,
--              -- what if the varaible case is done as ewll?  maybe not as
--              -- simple.
--              -- In the variable case, is it even solveable?
--              -- maybe this can force us to not even consider this one?
--              -- maybe Lambda case can be caught.  and it would show up here
--              -- as  right.  auto-evaluate for Lambdas.  yaaah.
--              TP o ts      -> case traverse' (either (\etw -> Just (Const [etw])) (const Nothing) . go) ts of
--                                -- hm there is a problem here.  what to
--                                -- return if there is some variable or
--                                -- something not reduceable?  this would
--                                -- happen if there was an unbound variable.
--                                -- i wonder if i could write a way to
--                                -- evaluate exprp that returns types, that
--                                -- could account for unbound variables.  but
--                                -- what would i even return if there were
--                                -- unbound variables?  basically that would
--                                -- be like (a -> b) bound to an a.  i guess
--                                -- that could only happen if it was
--                                -- introduced with lambda before??? maybe
--                                -- it's good
--                                -- but here we're basically relying on the
--                                -- fact that all cases will eventually not
--                                -- lead to Nothing.
--                                -- or well, the result can have unbound
--                                -- variables too, right? ... maybe just
--                                -- leave as V?
--                                -- but TP constructor...oops.
--                                -- hm maybe return an ExprP that only likes
--                                -- ExprP ETypes?
--                                Nothing -> undefined
--                                -- Right _ -> undefined
--                                -- Left (ETW t) -> 
--              -- TP o ts  -> Left (f t)
--              -- OP Ap (TP EStar :< _) (LambdaP (TP EStar) eλ :> et) -> go $ subIxorsP (g et) eλ
--              OP o _ es  -> O o <$> traverse' go es
--              LambdaP _ eλ -> Lambda <$> go eλ
--       where
--         g :: forall c d.
--              ExprP us (EType c)
--           -> Indexor (EType c ': us) d
--           -> ExprP us d
--         g t IZ = t
--         g _ (IS ix) = VP ix
--         -- comper :: forall us b. Either ETypeW (Expr us b) -> Either ETypeW :.: Expr us
--         -- comper = Comp


-- fromExprP' :: forall vs r a. (forall b. EType b -> r) -> ExprP vs a -> Either r (Expr (DeLambdaList vs) (DeLambda a))
-- fromExprP' f = go
--   where
--     go :: forall us b. ExprP us b -> Either r (Expr (DeLambdaList us) (DeLambda b))
--     go e = case e of
--              VP ix -> Right (V (deLambdaIx ix))
--              TP t  -> Left (f t)
--              O0p o _ -> case o of
--                           I i  -> Right $ O0 (I i)
--                           B b  -> Right $ O0 (B b)
--                           Unit -> Right $ O0 Unit
--                           Nil  -> Right $ O0 Nil
--              O1p o _ e1 -> case o of
--                              Abs    -> O1 Abs <$> go e1
--                              Signum -> O1 Signum <$> go e1
--                              Not    -> O1 Not <$> go e1
--                              Left'  -> O1 Left' <$> go e1
--                              Right' -> O1 Right' <$> go e1
--                              Fst    -> O1 Fst <$> go e1
--                              Snd    -> O1 Snd <$> go e1
--              O2p o ts e1 e2 -> case o of
--                                  Plus -> O2 Plus <$> go e1 <*> go e2
--                                  Times -> O2 Times <$> go e1 <*> go e2
--                                  Minus -> O2 Minus <$> go e1 <*> go e2
--                                  LEquals -> O2 LEquals <$> go e1 <*> go e2
--                                  And -> O2 And <$> go e1 <*> go e2
--                                  Or -> O2 Or <$> go e1 <*> go e2
--                                  Tup -> O2 Tup <$> go e1 <*> go e2
--                                  Cons -> O2 Cons <$> go e1 <*> go e2
--                                  Ap -> case (ts, e1, e2) of
--                                          -- so can apply
--                                          (TP EStar :< _, LambdaP (TP EStar) eλ, et) -> go $ subIxorsP (g et) eλ
--                                          (_, LambdaP et eλ, _)  -> O2 Ap <$> (Lambda <$> go eλ) <*> go e2
--                                          -- problem here ... wants to turn
--                                          -- ExprP (a -> b) into Expr
--                                          -- (DeLambda a -> DeLambda b), but
--                                          -- really should be turning it
--                                          -- into DeLambda (a -> b)
--                                          -- (_, _, _) -> O2 Ap <$> (_ e1) <*> go e2
--                                          -- (TP EStar :< _, VP ix, et) -> Right $ V (deLambdaIx ix)
--                                          -- (TP EStar :< _, VP ix, _) -> O2 Ap _ <$> go e2
--                                          -- (_, TP _, _)  -> undefined
--                                          (TP EInt :> TP EInt, _, _) -> O2 Ap <$> go e1 <*> go e2
--                                          -- (TP EInt :< _, _, _) -> do
--                                          --   O2 Ap e1' e2' <- O2 Ap <$> go e1 <*> go e2
--                                          --   return $ O2 Ap (_ e1') e2'
--                                  Div -> O2 Div <$> go e1 <*> go e2
--                                  Mod -> O2 Mod <$> go e1 <*> go e2
--              O3p o ts e1 e2 e3 -> case o of
--                                     If -> O3 If <$> go e1 <*> go e2 <*> go e3
--                                 -- Case -> O3 If (go e1) (go e2) (go e3)
--                                 -- UnfoldrN -> O3 UnfoldrN (go e1) (go e2) (go e3)
--                                 -- Foldr -> O3 Foldr (go e1) (go e2) (go e3)
--       where
--         g :: forall c d.
--              ExprP us (EType c)
--           -> Indexor (EType c ': us) d
--           -> ExprP us d
--         g t IZ = t
--         g _ (IS ix) = VP ix

--                        Unit -> O0 Unit
--                        Nil  -> O0 Nil
             -- OP o _ es -> O o <$> traverse' go es
    -- go e = case e of
    --          VP ix    -> Right (V ix)
    --          TP t     -> Left (f t)
    --          OP Ap (TP EStar :< _) (LambdaP (TP EStar) eλ :> et) -> go $ subIxorsP (g et) eλ
    --          OP o _ es  -> O o <$> traverse' go es
    --          LambdaP _ eλ -> Lambda <$> go eλ
    --   where
    --     g :: forall c d.
    --          ExprP us (EType c)
    --       -> Indexor (EType c ': us) d
    --       -> ExprP us d
    --     g t IZ = t
    --     g _ (IS ix) = VP ix


type family DeLambda (f :: *) :: * where
    DeLambda (EType a -> b) = b
    DeLambda (Either a b)   = Either (DeLambda a) (DeLambda b)
    DeLambda (a, b)         = (DeLambda a, DeLambda b)
    DeLambda [a]            = [DeLambda a]
    DeLambda a              = a

type family DeLambdaList (xs :: [*]) :: [*] where
    DeLambdaList '[]       = '[]
    DeLambdaList (a ': as) = DeLambda a ': DeLambdaList as

-- omg...does this actually work?
-- have to work on removing redundant lambas, but....this might actually be
-- it? :O :O :O
toExprT :: ExprP vs a -> Maybe (ExprTy (LengthList vs))
toExprT e = case e of
              VP ix -> Just $ VTy (ixFin ix)
              TP o ts -> TTy o . pToVec <$> traverse' (fmap Const . toExprT . getComp) ts
              -- okay we're at a crossroads here.  the result can't depend
              -- on any values...so ignore es.  only look at ts?
              OP o ts _ -> opToT o ts
              LambdaP _ eλ -> Forall <$> toExprT eλ
              -- LambdaP et eλ -> do
              --   et' <- toExprT et
              --   undefined
                -- _


-- such unsafe!!!  nothing is compiler verified!
-- wait noooo this is all wrong...is supposed to return the type if it
-- contains a type!!!!!! aaahhhh!!!
opToT' :: Op ts as a -> ExprPETList vs ts -> Maybe (ExprTy (LengthList vs))
opToT' o ts =
    case o of
      I _ -> Just (TTy TOInt ØV)
      B _ -> Just (TTy TOBool ØV)
      Nil -> case ts of
               Comp t :< Ø -> TTy TOList . pure <$> toExprT t
               _ -> impossible ""
      Unit -> Just (TTy TOUnit ØV)

      Abs -> Just (TTy TOInt ØV)
      Signum -> Just (TTy TOInt ØV)
      Not -> Just (TTy TOBool ØV)
      Left' -> case ts of
                 Comp t1 :< Comp t2 :< Ø -> do
                   t1' <- toExprT t1
                   t2' <- toExprT t2
                   return $ TTy TOEither (t1' :+ t2' :+ ØV)
                 _ -> impossible ""
      Right' -> case ts of
                 Comp t1 :< Comp t2 :< Ø -> do
                   t1' <- toExprT t1
                   t2' <- toExprT t2
                   return $ TTy TOEither (t1' :+ t2' :+ ØV)
                 _ -> impossible ""
      Fst -> case ts of
               Comp t :< _ :< Ø -> toExprT t
               _ -> impossible ""
      Snd -> case ts of
               _ :< Comp t :< Ø -> toExprT t
               _ -> impossible ""
      Plus -> Just (TTy TOInt ØV)
      Times -> Just (TTy TOInt ØV)
      Minus -> Just (TTy TOInt ØV)
      LEquals -> Just (TTy TOBool ØV)
      And -> Just (TTy TOBool ØV)
      Or -> Just (TTy TOBool ØV)
      Tup -> case ts of
               Comp t1 :< Comp t2 :< Ø -> do
                 t1' <- toExprT t1
                 t2' <- toExprT t2
                 return $ TTy TOTup (t1' :+ t2' :+ ØV)
               _ -> impossible ""
      Cons -> case ts of
                Comp t :< Ø -> TTy TOList . pure <$> toExprT t
                _ -> impossible ""
      Ap -> case ts of
              _ :< Comp t :< Ø -> toExprT t
              _ -> impossible ""
      Div -> Just (TTy TOEither (TTy TOUnit ØV :+ TTy TOInt ØV :+ ØV))
      Mod -> Just (TTy TOEither (TTy TOUnit ØV :+ TTy TOInt ØV :+ ØV))
      If -> case ts of
              Comp t :< Ø -> toExprT t
              _ -> impossible ""
      Case -> case ts of
                _ :< _ :< Comp t :< Ø -> toExprT t
                _ -> impossible ""
      UnfoldrN -> case ts of
                    _ :< Comp t :< Ø -> TTy TOList . pure <$> toExprT t
                    _ -> impossible ""
      Foldr -> case ts of
                 _ :< Comp t :< Ø -> toExprT t
                 _ -> impossible ""
               
opToT :: Op ts as a -> ExprPETList vs ts -> Maybe (ExprTy (LengthList vs))
opToT o ts =
    case o of
      I _ -> Nothing
      B _ -> Nothing
      Nil -> Nothing -- nonsense?? [EType a]?
      Unit -> Nothing

      Abs -> Nothing
      Signum -> Nothing
      Not -> Nothing
      Left' -> Nothing -- nonsense?  Either (EType a) b ?
      Right' -> Nothing
      Fst -> case ts of
               Comp t :< _ :< Ø -> TTy TOTup . pure <$> toExprT t
               _ -> impossible ""
      Snd -> case ts of
               _ :< Comp t :< Ø -> TTy TOTup . pure <$> toExprT t
               _ -> impossible ""
      Plus -> Nothing
      Times -> Nothing
      Minus -> Nothing
      LEquals -> Nothing
      And -> Nothing
      Or -> Nothing
      Tup -> Nothing
      Cons -> Nothing -- right?
      Ap -> case ts of
              _ :< Comp t :< Ø -> toExprT t
              _ -> impossible ""
      Div -> Nothing
      Mod -> Nothing
      If -> case ts of
              Comp t :< Ø -> toExprT t
              _ -> impossible ""
      Case -> case ts of
                _ :< _ :< Comp t :< Ø -> toExprT t
                _ -> impossible ""
      UnfoldrN -> Nothing
      Foldr -> case ts of
                 _ :< Comp t :< Ø -> toExprT t
                 _ -> impossible ""

-- op :: Op ts as a -> HList as -> a
-- op o xs = case o of
--             I i      -> i
--             B b      -> b
--             Nil      -> []
--             Unit     -> ()
--             Abs      -> overHL1 abs xs
--             Signum   -> overHL1 signum xs
--             Not      -> overHL1 not xs
--             Left'    -> overHL1 Left xs
--             Right'   -> overHL1 Right xs
--             Fst      -> overHL1 fst xs
--             Snd      -> overHL1 snd xs
--             Plus     -> overHL2 (+) xs
--             Times    -> overHL2 (*) xs
--             Minus    -> overHL2 (-) xs
--             LEquals  -> overHL2 (<=) xs
--             And      -> overHL2 (&&) xs
--             Or       -> overHL2 (||) xs
--             Tup      -> overHL2 (,) xs
--             Cons     -> overHL2 (:) xs
--             Ap       -> overHL2 ($) xs
--             Div      -> overHL2 (\x y -> if y == 0 then Left () else Right (x `div` y)) xs
--             Mod      -> overHL2 (\x y -> if y == 0 then Left () else Right (x `mod` y)) xs
--             If       -> overHL3 (\b x y -> if b then x else y) xs
--             Case     -> overHL3 (\e l r -> either l r e) xs
--             UnfoldrN -> overHL3 (\n f z -> take n (unfoldr (Just . f) z)) xs
--             Foldr    -> overHL3 foldr xs


ixFin :: Indexor vs a -> Fin (LengthList vs)
ixFin IZ = FZ
ixFin (IS ix) = FS (ixFin ix)

pToVec :: Prod (Const a) as -> V (LengthList as) a
pToVec Ø = ØV
pToVec (Const x :< xs) = pure x :* pToVec xs

-- pToVec' :: Prod (Const (ExprTy (LengthList vs))) (EType L.<$> as) -> V (LengthList as) (ExprTy (LengthList vs))
-- pToVec' = undefined

-- compProd :: (LengthList (g L.<$> as) ~ LengthList as) => Prod f (g L.<$> as) -> Prod (f :.: g) as
-- compProd Ø = Ø

-- deLambda :: Expr vs a -> Expr (DeLambdaList vs) (DeLambda a)
-- deLambda = go
--   where
--     go :: forall us b. Expr us b -> Expr (DeLambdaList us) (DeLambda b)
--     go e = case e of
--              V ix   -> V (deLambdaIx ix)
--              O0 o -> case o of
--                        I i  -> O0 (I i)
--                        B b  -> O0 (B b)
--                        Unit -> O0 Unit
--                        Nil  -> O0 Nil
--              O1 o e1 -> case o of
--                           Abs    -> O1 Abs (go e1)
--                           Signum -> O1 Signum (go e1)
--                           Not    -> O1 Not (go e1)
--                           Left'  -> O1 Left' (go e1)
--                           Right' -> O1 Right' (go e1)
--                           Fst    -> O1 Fst (go e1)
--                           Snd    -> O1 Snd (go e1)
--              O2 o e1 e2 -> case o of
--                              Plus -> O2 Plus (go e1) (go e2)
--                              Times -> O2 Times (go e1) (go e2)
--                              Minus -> O2 Minus (go e1) (go e2)
--                              LEquals -> O2 LEquals (go e1) (go e2)
--                              And -> O2 And (go e1) (go e2)
--                              Or -> O2 Or (go e1) (go e2)
--                              Tup -> O2 Tup (go e1) (go e2)
--                              Cons -> O2 Cons (go e1) (go e2)
--                              -- Ap -> O2 Ap (go e1) (go e2)
--                              Ap -> case (e1, e2) of
--                                      (Lambda eλ, et) -> undefined
--                                      -- problem here. we can only plug in
--                                      -- polies if we know it's an EType,
--                                      -- but we don't know it's an EType
--                                      -- from this.
--                              Div -> O2 Div (go e1) (go e2)
--                              Mod -> O2 Mod (go e1) (go e2)
--              O3 o e1 e2 e3 -> case o of
--                                 If -> O3 If (go e1) (go e2) (go e3)
--                                 -- Case -> O3 If (go e1) (go e2) (go e3)
--                                 -- UnfoldrN -> O3 UnfoldrN (go e1) (go e2) (go e3)
--                                 -- Foldr -> O3 Foldr (go e1) (go e2) (go e3)
--              -- Lambda eλ -> Lambda (go eλ)

deLambdaIx :: Indexor vs a -> Indexor (DeLambdaList vs) (DeLambda a)
deLambdaIx IZ      = IZ
deLambdaIx (IS ix) = IS (deLambdaIx ix)

-- applyEType :: (forall a. Expr vs (EType a -> b)) -> EType b
-- applyEType = undefined

-- reduceAll :: Expr vs a -> Expr vs a
-- reduceAll e | e == e'   = e'
--             | otherwise = reduceAll e'
--   where
--     Identity e' = traverseExprPrePostM (Identity . collapse) e

-- collapse :: Expr vs a -> Expr vs a
-- collapse e = case e of
--                V ix -> V ix
--                O0 o -> O0 o
--                O1 o e1 -> case o of
--                             Fst    -> case e1 of
--                                         O2 Tup ex _ -> ex
--                                         _           -> e
--                             Snd    -> case e1 of
--                                         O2 Tup _ ey -> ey
--                                         _           -> e
--                             o'     -> case e1 of
--                                         O0 o'' -> case op1_ o' (op0 o'') of
--                                                     Just x -> O0 x
--                                                     _      -> O1 o e1
--                                         _      -> O1 o e1
--                O2 o e1 e2 -> case o of
--                                Mod -> collapseModDiv Mod e1 e2
--                                Div -> collapseModDiv Div e1 e2
--                                Ap  -> collapseAp e1 e2
--                                o'  -> case (e1, e2) of
--                                         (O0 o''1, O0 o''2) ->
--                                           case op2_ o' (op0 o''1) (op0 o''2) of
--                                             Just x -> O0 x
--                                             _      -> O2 o e1 e2
--                                         _   -> e
--                O3 o e1 e2 e3 -> case o of
--                                   If       -> collapseIf e1 e2 e3
--                                   Case     -> collapseCase e1 e2 e3
--                                   UnfoldrN -> collapseUnfoldrN e1 e2 e3
--                                   Foldr    -> collapseFoldr e1 e2 e3
--                Lambda eλ -> Lambda eλ
--   where
--     collapseModDiv :: Op2 Int Int (Maybe' Int) -> Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
--     collapseModDiv o2 ex ey = case (ex, ey) of
--                               (O0 (I x), O0 (I y)) -> case op2 o2 x y of
--                                                         Left () -> O1 Left' (O0 Unit)
--                                                         Right z -> O1 Right' (O0 (I z))
--                               _                    -> O2 o2 ex ey
--     collapseAp :: forall vs a b. Expr vs (a -> b) -> Expr vs a -> Expr vs b
--     collapseAp ef ex = case ef of
--                          Lambda eλ -> subVariables apply eλ
--                          _         -> ef ~$ ex
--       where
--         apply :: forall c. Indexor (a ': vs) c -> Expr vs c
--         apply IZ      = ex
--         apply (IS ix) = V ix
--     collapseIf :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr vs a
--     collapseIf eb ex ey = case eb of
--                             O0 (B b) | b         -> ex
--                                      | otherwise -> ey
--                             _                    -> if' eb ex ey
--     collapseCase :: Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs c
--     collapseCase ee el er = case ee of
--                               O1 Left' ex  -> el ~$ ex
--                               O1 Right' ex -> er ~$ ex
--                               _                  -> case' ee el er
--     collapseUnfoldrN :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> Expr vs [b]
--     collapseUnfoldrN en ef ez = case en of
--                                 O0 (I i) | i <= 0    -> nil'
--                                          | otherwise -> unfold (i - 1)
--                                 _                    -> unfoldrN' en ef ez
--       where
--         unfold i = (λ .-> fst' (V IZ) ~: unfoldrN' (iI i)
--                                                    (overIxors IS ef)
--                                                    (snd' (V IZ))
--                    ) ~$ (ef ~$ ez)
--     collapseFoldr :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> Expr vs b
--     collapseFoldr ef ez exs = case exs of
--                                 O0 Nil         -> ez
--                                 O2 Cons ey eys -> ef ~$ ey ~$ foldr' ef ez eys
--                                 _              -> foldr' ef ez exs

-- subVariables :: forall vs us a. (forall b. Indexor vs b -> Expr us b) -> Expr vs a -> Expr us a
-- subVariables f = runIdentity . subVariablesA (Identity . f)

-- subVariablesA :: forall vs us f a. Applicative f => (forall b. Indexor vs b -> f (Expr us b)) -> Expr vs a -> f (Expr us a)
-- subVariablesA f = go
--   where
--     go :: forall b. Expr vs b -> f (Expr us b)
--     go e = case e of
--              V ix          -> f ix
--              O0 o          -> pure $ O0 o
--              O1 o e1       -> O1 o <$> go e1
--              O2 o e1 e2    -> O2 o <$> go e1 <*> go e2
--              O3 o e1 e2 e3 -> O3 o <$> go e1 <*> go e2 <*> go e3
--              Lambda eλ     -> Lambda <$> subVariablesA f' eλ
--     f' :: forall b c. Indexor (c ': vs) b -> f (Expr (c ': us) b)
--     f' IZ      = pure $ V IZ
--     f' (IS ix) = subVariables (V . IS) <$> f ix

-- will this be good enough for monomorphic cases?
-- might have to resort to doing something with Proxy and letting people
-- manually state.
--
-- looks like it defers to "push as much as possible", which maybe or maybe
-- not be the best desire for monomorphic code...

-- class PushInto vs us where
--     pushInto :: Expr vs a -> Expr us a

-- instance PushInto vs vs where
--     pushInto = id

-- instance PushInto vs us => PushInto vs (v ': us) where
--     pushInto = overIxors IS . pushInto

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

tOp :: TOp as a -> Prod EType as -> EType a
tOp o xs = case o of
             TOStar   -> EStar
             TOInt    -> EInt
             TOBool   -> EBool
             TOUnit   -> EUnit
             TOList   -> uncurry'1 EList xs
             TOEither -> uncurry'2 EEither xs
             TOTup    -> uncurry'2 ETup xs
             TOFunc   -> uncurry'2 EFunc xs

op :: Op ts as a -> HList as -> a
op o xs = case o of
            I i      -> i
            B b      -> b
            Nil      -> []
            Unit     -> ()
            Abs      -> overHL1 abs xs
            Signum   -> overHL1 signum xs
            Not      -> overHL1 not xs
            Left'    -> overHL1 Left xs
            Right'   -> overHL1 Right xs
            Fst      -> overHL1 fst xs
            Snd      -> overHL1 snd xs
            Plus     -> overHL2 (+) xs
            Times    -> overHL2 (*) xs
            Minus    -> overHL2 (-) xs
            LEquals  -> overHL2 (<=) xs
            And      -> overHL2 (&&) xs
            Or       -> overHL2 (||) xs
            Tup      -> overHL2 (,) xs
            Cons     -> overHL2 (:) xs
            Ap       -> overHL2 ($) xs
            Div      -> overHL2 (\x y -> if y == 0 then Left () else Right (x `div` y)) xs
            Mod      -> overHL2 (\x y -> if y == 0 then Left () else Right (x `mod` y)) xs
            If       -> overHL3 (\b x y -> if b then x else y) xs
            Case     -> overHL3 (\e l r -> either l r e) xs
            UnfoldrN -> overHL3 (\n f z -> take n (unfoldr (Just . f) z)) xs
            Foldr    -> overHL3 foldr xs

overHL1 :: (a -> b) -> HList '[a] -> b
overHL1 f = runIdentity . uncurry'1 (fmap f)
overHL2 :: (a -> b -> c) -> HList '[a, b] -> c
overHL2 f = runIdentity . uncurry'2 (liftA2 f)
overHL3 :: (a -> b -> c -> d) -> HList '[a, b, c] -> d
overHL3 f = runIdentity . uncurry'3 (liftA3 f)

-- overProd1 :: forall a b. (a -> b) -> Prod f '[a] -> f b
-- overProd1 f (x :<- Ø) = f x
-- overProd1 _ _ = error "impossible"
-- overProd2 :: forall a b c. (a -> b -> c) -> Prod f '[a, b] -> f c
-- overProd2 f (x :<- (y :<- Ø)) = f x y
-- overProd2 _ _ = error "impossible"
-- overProd3 :: forall a b c d. (a -> b -> c -> d) -> Prod f '[a, b, c] -> f d
-- overProd3 f (x :<- (y :<- (z :<- Ø))) = f x y z
-- overProd3 _ _ = error "impossible"

-- op1_ :: Op1 a b -> a -> Maybe (Op0 b)
-- op1_ o = modder . op1 o
--   where
--     modder = case o of
--                Abs    -> Just . I
--                Signum -> Just . I
--                Not    -> Just . B
--                Left'  -> const Nothing
--                Right' -> const Nothing
--                Fst    -> const Nothing
--                Snd    -> const Nothing

-- op2_ :: Op2 a b c -> a -> b -> Maybe (Op0 c)
-- op2_ o x y = modder (op2 o x y)
--   where
--     modder = case o of
--                Plus    -> Just . I
--                Times   -> Just . I
--                Minus   -> Just . I
--                LEquals -> Just . B
--                And     -> Just . B
--                Or      -> Just . B
--                Tup     -> const Nothing
--                Cons    -> const Nothing
--                Ap      -> const Nothing
--                Div     -> const Nothing
--                Mod     -> const Nothing

-- lengthHList :: HList vs -> Int
-- lengthHList HNil = 0
-- lengthHList (_ :< xs) = 1 + lengthHList xs

