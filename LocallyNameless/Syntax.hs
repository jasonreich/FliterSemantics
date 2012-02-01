{-# LANGUAGE ParallelListComp, DeriveFunctor #-}
module Syntax where

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Miniplate

-- Basic abstract syntax tree
type Id = String
type Ix = Int

data V free = Fre free
            | Bnd Ix
            deriving (Show, Eq, Functor)
                     
bmap :: (Int -> Int) -> V free -> V free
bmap f (Fre x) = Fre x
bmap f (Bnd i) = Bnd (f i)

data Op = Pl | Mi | Eq | Ne | Le | Seq
        deriving (Show, Eq)

data Expr free = Var (V free)
               | Fun Ix [free]
               | Con Id [free]
               | PVa Int
               | POp Op (V free) (V free)
               | Expr free :@ [V free]
               | Let [Expr free] (Expr free)
               | Case (Expr free) [Alte free]
               deriving (Eq, Functor)

data Alte free = (Id, Ix) :-> Expr free
               deriving (Eq, Functor)
                        
data Func free = Lam Ix (Expr free)
               deriving (Eq, Functor)

newtype Prog free = Prog [Func free]
               deriving (Eq, Functor)

isWHNF :: Prog free -> Expr free -> Bool
isWHNF (Prog fs) (Con _ _)  = True
isWHNF (Prog fs) (Fun f vs) = case drop f fs of
  [] -> True
  (Lam novs _:_) -> length vs < novs
isWHNF (Prog fs) (PVa _)    = True
isWHNF _         _          = False

-- Tree traversals
instance Uniplate (Expr free) where
  uniplate (x :@ vs)   = B [x] $ \[x] -> x :@ vs
  uniplate (Let xs y)  = B (y:xs) $ \(y:xs) -> Let xs y
  uniplate (Case x as) = B (x : [ y | _ :-> y <- as ]) 
                         $ \(x:ys) -> Case x [ p :-> y 
                                             | p :-> _ <- as 
                                             | y <- ys ]
  uniplate x = B [] $ \[] -> x
  
-- Close terms

safeFree :: (Ix -> V free) -> (V free -> V free)
safeFree rho (Fre x) = Fre x
safeFree rho (Bnd v) = rho v

shift i rho = bmap (+ i) . rho . (+ (- i))

instantiate :: (Ix -> V free) -> Expr free -> Expr free
instantiate rho (Var v)     = Var (safeFree rho v)
instantiate rho (POp o v w) = POp o (safeFree rho v) (safeFree rho w)
instantiate rho (x :@ vs)   = instantiate rho x :@ 
                              map (safeFree rho) vs
instantiate rho (Let xs y)  = Let (map (instantiate rho) xs)
                                  (instantiate (shift (length xs) rho) y)
instantiate rho (Case x as) = Case (instantiate rho x)
                              [ (c, vs) :-> instantiate (shift vs rho) y 
                              | ((c, vs) :-> y) <- as ]
instantiate _   x           = x

instantiate' xs = instantiate rho
  where len_xs = length xs
        rho i | i < 0      = Bnd $ i
              | i < len_xs = Fre $ xs !! i
              | otherwise  = Bnd $ i - len_xs

-- Open terms
safeBind :: (a -> V b) -> (V a -> V b)
safeBind rho (Fre x) = rho x
safeBind rho (Bnd v) = Bnd v

abstract :: (a -> V b) -> Expr a -> Expr b
abstract rho (Var v)     = Var (safeBind rho v)
abstract rho (Fun f vs)  = Fun f [] :@ map rho vs
abstract rho (Con c vs)  = Con c [] :@ map rho vs
abstract rho (PVa n)     = PVa n
abstract rho (POp o v w) = POp o (safeBind rho v) (safeBind rho w)
abstract rho (x :@ vs)   = abstract rho x :@ map (safeBind rho) vs
abstract rho (Let xs y)  = Let (map (abstract rho) xs)
                           (abstract (bmap (+ length xs) . rho) y)
abstract rho (Case x as) = Case (abstract rho x)
                           [ (c, vs) :-> abstract (bmap (+ vs) . rho) y 
                           | ((c, vs) :-> y) <- as ]

abstract' xs = abstract rho
  where rho x = maybe (Fre x) Bnd $ elemIndex x xs
        
freeVars :: Ord a => Expr a -> Set a
freeVars (Var (Fre x)) = Set.singleton x
freeVars (Con _ vs)    = Set.fromList vs
freeVars (Fun _ vs)    = Set.fromList vs
freeVars (POp _ v w)   = Set.fromList [ x | Fre x <- [v, w] ]
freeVars (x :@ vs)     = freeVars x `Set.union` Set.fromList [ v | Fre v <- vs ]
freeVars x             = extract freeVars x