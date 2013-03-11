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

-- Choisir l'une des zones de la liste lz
sczChooseZone objs lz = do
  -- On construit le PL et on récupère les id des variables représentant les objectifs
--  objs <- domain
  
  -- On crée une variable de décision {0-1} par zone  
  s <- get
  z <- foldM (\l v -> do 
                 zi <- supplyNew
                 setVarKind zi BinVar 
                 return $ zi:l) [] lz
  -- Pour chaque objectif k, on construit la somme du terme de droite de la contrainte     
  -- (<= somme (vzik + 1) * zi pour toutes zone i
  let ctrs = foldl (\a (zi,vz) -> zipWith (++) a [[(vzk + 1, zi)] | vzk <- vz]  ) (take (length objs) (repeat [])) (zip z lz) 
      
  foldM (\_ (cxk,ct) -> linCombination [(1,cxk)] `geq` linCombination ct ) ()  $ zip objs ctrs
  

  
  setObjective $ linCombination $ zip [1..] z
  setDirection Min
  writeLPToFile "test.lp"
  ans <- quickSolveMIP
  put s
  return ans
sczGetNewPoint objs vz = do
  --objs <- domain
  s <- get
  foldM (\_ (cxk,vzk) -> varSum [cxk] `geqTo` (vzk + 1) ) () $ zip objs vz
  ans <- quickSolveMIP 
  put s
  return ans 
  {-
-- Relation de dominance
x /\ y = (and $ zipWith (>=) x y)  && x /= y 
buildzj vzi j  xj = map (\(i,t) -> if i == j then xj else t) $ zip [1..] vzi 
-- Supprime la zone couverte par x, ajoute celles induites par x
-- retourne la nouvelle liste de zones.
sczAddZone x lz current = let --(l,l') = break (x /\) lz
                               (vz,l) = foldl (\(vz',lz') zi -> if x /\ zi then (zi:vz',lz') else (vz',x:lz')) ([],[]) lz
                      
                               new = nub $ (concat [ [buildzj vzi j xj | (j,xj) <- zip [1..] x] | vzi <- vz] )
                          in  [zi | zi <- new, not $ or [zi /\ xi | xi <- new, xi /= zi]] ++ l

scz' domain lz pts objs = if null lz && null pts
                          then do
                            objs <- domain
                           -- s <- get
                            (ret,sol) <- sczGetNewPoint objs $ repeat 0
                            case ret of
                              Success -> let (opt,ans) = fromJust sol
                                             pt = map (ans!) objs
                                             lz' = sczAddZone pt [take (length objs) $ repeat 0]
                                         in trace ("lz=" ++ show lz' ++ "\t" ++ "adding " ++ show pt ) 
                                                  scz' domain lz' (pt:pts) objs
  
                              otherwise -> return pts
                          else if null lz then return pts
                          else do
                           
                            -- On résoud le problème de choisir une zone
                            (ret,sol) <- sczChooseZone objs lz
                           
                            
                            case ret of
                              Success -> let (opt,ans) = fromJust sol
                                             pt = map (ans !) objs
                                             zone = trace ("OPT=" ++ show ans) $  lz !! ((fromIntegral $ truncate opt) - 1)
                                         in if opt > 0 then do
                                           (ret',sol') <- sczGetNewPoint objs zone
                                           case ret' of
                                             Success -> let (opt',ans') = fromJust sol'
                                                            xstar = map (ans' ! ) objs
                                                            lz' = sczAddZone xstar lz
                                                        in trace ("lz=" ++ show lz' ++ "\t adding" ++ show xstar  ++ "\t zone exploree=" ++ show zone ++ "\t pt=" ++ show pt) scz' domain lz' (xstar:pts) objs
                                             otherwise -> let lz' = sczAddZone pt lz
                                                          in trace ("lz=" ++ show lz' ++ "\t adding" ++ show pt ++ "\t [Empty zone]") scz' domain lz' (pt:pts) objs
                                          else trace "OPT = 0" return pts
                              otherwise -> return pts
-}                                           
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