{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.ExprGADT.Pretty (showPretty, printPretty) where

import Data.ExprGADT.Types
import Control.Monad.State
import Data.List
import Control.Monad.Reader
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type Var = String
type Env = IntMap ()

data VarStack = VS { vsBound :: [Var]
                   , vsPool  :: [Var]
                   }

data Fixity = InfixL | InfixR | Infix deriving Eq

data Operator = Opr { _oprFixity :: Fixity
                    , _oprPrec   :: Int
                    , _oprShow   :: String
                    }

printPretty :: Expr vs x -> IO ()
printPretty = putStrLn . showPretty

showPretty :: Expr vs x -> String
showPretty e = envOut . res 0 $ ""
  where
    envOut :: ShowS
    envOut | IM.null env = showString ""
           | otherwise   = let envs = map (\s -> '$':show s) (IM.keys env)
                               envStr = intercalate "," envs
                           in showString ("[" ++ envStr ++ "]: ")
    res :: Int -> ShowS
    (res, env) = runState (runReaderT (exprShower e) vs0) IM.empty
    vs0 :: VarStack
    vs0 = VS [] varNames
    varNames :: [String]
    varNames = [ v : if n == 0 then "" else show (n :: Int)
               | n <- [0..]
               , v <- "xyzhijklmnpqrstuvw"]


exprShower :: (MonadReader VarStack m, MonadState Env m)
           => Expr vs a
           -> m (Int -> ShowS)
exprShower = exprShower' (showString "\\")

exprShower' :: (MonadReader VarStack m, MonadState Env m)
            => ShowS
            -> Expr vs a
            -> m (Int -> ShowS)
exprShower' l e = case e of
                    V ix -> do
                      let i = indexorLength ix
                      bounds <- asks vsBound
                      let env = i - length bounds + 1
                      if env > 0
                        then do
                          addEnv env
                          return $ \_ -> showString ('$':show env)
                        else
                          return $ \_ -> showString (bounds !! i)
                    O0 o -> return $ printOp0 o
                    O1 o e1 -> do
                      e1S <- exprShower e1
                      return $ showOp oprAp (\_ -> printOp1 o) e1S
                    O2 o e1 e2 -> do
                      e1S <- exprShower e1
                      e2S <- exprShower e2
                      return $ case o of
                        Tup -> \_ -> showParen True
                                       $ e1S 10
                                       . showString ", "
                                       . e2S 10
                        _   -> showOp (oprOp2 o) e1S e2S
                    O3 o e1 e2 e3 -> do
                      let isCase = case o of
                                     Case -> True
                                     _    -> False
                      e1S <- exprShower e1
                      e2S <- if isCase
                               then exprShower' (showString "Right ") e2
                               else exprShower e2
                      e3S <- if isCase
                               then exprShower' (showString "Left ") e3
                               else exprShower e3
                      return $ \p -> case o of
                        If -> showParen (p > 0)
                                $ showString "if "
                                . e1S 0
                                . showString " then "
                                . e2S 0
                                . showString " else "
                                . e3S 0
                        Case -> showParen (p > 0)
                                  $ showString "case "
                                  . e1S 0
                                  . showString " of "
                                  . e2S 0
                                  . showString "; "
                                  . e3S 0
                        UnfoldrN -> ( (\_ -> showString "unfoldrN")
                                   $* e1S
                                   $* e2S
                                   $* e3S ) p
                        Foldr -> ( (\_ -> showString "foldr")
                                $* e1S
                                $* e2S
                                $* e3S ) p
                    Lambda eλ -> do
                      eλS <- local popVar $ exprShower eλ
                      v <- asks $ head . vsPool
                      return $ \p -> showParen (p > 0)
                                       $ l
                                       . showString v
                                       . showString " -> "
                                       . eλS 0


    -- If       :: Op3 Bool a a a
    -- Case     :: Op3 (Either a b) (a -> c) (b -> c) c
    -- UnfoldrN :: Op3 Int (a -> (b, a)) a [b]
    -- Foldr    :: Op3 (a -> b -> b) b [a] b

        -- O1 op e1 -> do
        --     e1' <- showExpr e1 vs
        --     return $ showAp (const $ showString (op1 op)) e1'
  where
    infixl 1 $*
    f $* x = showOp oprAp f x
    showOp :: Operator -> (Int -> ShowS) -> (Int -> ShowS) -> Int -> ShowS
    showOp (Opr fixity prec op) e1 e2 p = showParen (p > prec)
                                            $ e1 (if fixity == InfixL then prec else prec + 1)
                                            . showString op
                                            . e2 (if fixity == InfixR then prec else prec + 1)
printOp0 :: Op0 a -> Int -> ShowS
printOp0 (I i) = flip showsPrec i
printOp0 (B b) = flip showsPrec b
printOp0 Nil   = \_ -> showString "[]"
printOp0 Unit  = \_ -> showString "()"

printOp1 :: Op1 a b -> ShowS
printOp1 Abs    = showString "abs"
printOp1 Signum = showString "signum"
printOp1 Not    = showString "signum"
printOp1 Left'  = showString "Left"
printOp1 Right' = showString "Right"
printOp1 Fst    = showString "fst"
printOp1 Snd    = showString "snd"

oprOp2 :: Op2 a b c -> Operator
oprOp2 Plus    = Opr InfixL 6 " + "
oprOp2 Times   = Opr InfixL 7 " * "
oprOp2 Minus   = Opr InfixL 6 " - "
oprOp2 LEquals = Opr Infix  4 " <= "
oprOp2 And     = Opr InfixR 3 " && "
oprOp2 Or      = Opr InfixR 2 " || "
oprOp2 Tup     = Opr Infix  0 ", "
oprOp2 Cons    = Opr InfixR 5 ":"
oprOp2 Ap      = oprAp
oprOp2 Div     = Opr InfixL 7 " `div` "
oprOp2 Mod     = Opr InfixL 7 " `mod` "

oprAp :: Operator
oprAp = Opr InfixL 10 " "

addEnv :: MonadState Env m => Int -> m ()
addEnv i = modify $ IM.insert i ()

popVar :: VarStack -> VarStack
popVar (VS bs (v:vs)) = VS (v:bs) vs
popVar (VS bs [])     = VS ("OUT OF VARIABLES":bs) []
