module Sample.Knapsack (test) where

import Algorithms.Lokman

import Control.Monad
import Control.Applicative
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.LPMonad
import Control.Monad.LPMonad.Supply

import Data.Algebra
import qualified Data.Array as A
import Data.Maybe
import Data.Map.Lazy hiding (foldl,map,null)
import Data.List
import Data.LinearProgram.Common
import Data.LinearProgram.GLPK.Solver

import Debug.Trace

type Values = [Double]
type Weights = [Double]
type Capacity = Double

modelKnapSack :: [Values] -> [Weights] -> [Capacity] -> LPT Var Double (VSupplyT IO) [Var]
modelKnapSack values weights capacities = 
  let n = length $ head $ values
      p = length $ values
  in do
    x <- supplyN n
    setDirection Max
    objs <- supplyN p
    foldM (\_ e -> setVarKind e BinVar) () x
    foldM (\_ l -> addWeightedObjective (1/(1000*toRational p)) (linCombination [(1,l)]) ) () objs
    addObjective $ varSum [(last objs)]
    foldM (\_ (l,o) -> linCombination (zip l x) `equal` linCombination [(1,o)]) () $ zip values objs
    foldM (\_ (l,cmax) -> linCombination (zip l x) `leqTo` cmax ) () $ zip weights capacities
    return objs
    
-- Une zone est représenté par le pt qu'elle domine
type Zone = [Double]    


testVals = [[54, 64, 46, 37, 31, 62, 52, 33, 87, 35 ], 
            [52, 65, 58, 63, 46, 66, 72, 95, 42, 29],
            [56, 90, 34, 13, 71, 33, 66, 74, 88, 71]]
testWeights = [[52, 52, 28, 23, 95, 69, 13, 61, 32, 68],
               [88, 98, 49, 28, 43, 98, 53, 52, 84, 66],
               [57, 30, 86, 50, 97, 96, 59, 94, 67, 14]]
testCapacities = [246, 329, 325] 

testKS = modelKnapSack testVals testWeights testCapacities

test = do
  (x,_) <- runVSupplyT $ runLPT $ lokKok testKS 3
  putStrLn $ unlines $ map (show . A.elems) (elems x)
{-
test' = do
  (x,lp) <- runVSupplyT $ runLPT $ modelKnapSack testVals testWeights testCapacities >> quickSolveMIP
  print x

test = do
  (x,lp) <- runVSupplyT $ runLPT $ scz' (modelKnapSack testVals testWeights testCapacities) [] [] []
  putStrLn $ show x-}