{-# LANGUAGE OverloadedStrings #-}
module Algorithms.Lokman where

import Logs.Logs
import Control.Monad
import Control.Monad.Writer
import Control.Applicative hiding (empty)
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.LPMonad
import Control.Monad.LPMonad.Supply

import Data.Algebra
import Data.Maybe
import qualified Data.Array as A 
import Data.Map.Lazy hiding (foldl,map)
import Data.List hiding (insert)
import Data.LinearProgram.Common
import Data.LinearProgram.GLPK.Solver

import Text.LaTeX hiding (empty)

import Debug.Trace

fk=10

{- Notations :
 Sn : Ensemble des solutions ND déjà trouvées
 k = [k1...k(p-2)] : Représente le choix de la solution d'indice ki pour borne inf sur le critere i
 b = [b1...b(p-1)] : Vecteur des bornes infs sur chaque critère (pour les (p-1))
 Snk = Ensemble des solutions ND déjà trouvées valides pour le vecteur b associé à k 
       (en laissant libre la (p-1)e composante)
-}
infty = 9999999
inftyTab = A.array (1,3) $ zip [1..] $ repeat (- infty)
                
filterMap = Data.Map.Lazy.filter
filterList = Data.List.filter
-- Génère l'ensemble des permutations (vecteurs k) valides, c'est à dire respectant :
-- (i) : zki + 1 <= zkj pour tout i,j avec i < j
buildK sn p = runCont (buildK' sn [] 1 p) id
buildK' :: Map Integer (A.Array Integer Double) ->
          [Integer] ->
          Integer ->
          Integer ->
          Cont r [(Map Integer (A.Array Integer Double), [Integer])]
buildK' snk kpart i imax  = if i > imax then return [(snk, reverse kpart)]
                            else foldM (\ l (ki,xi) -> do l' <- buildK' (if ki /= 0 then filterMap (f xi) snk
                                                                         else snk) (ki:kpart) (i+1) imax 
                                                          return $ l ++ l') [] ((0,inftyTab):assocs snk) 
    where f xi xj = xj A.! i > xi A.! i
          

-- Génère le vecteur b à partir d'un vecteur k et de l'ensemble Snk
buildB :: Map Integer (A.Array Integer Double) ->
          Integer ->
          [Integer] ->
          Map Integer (A.Array Integer Double) ->
          [Double]
buildB sn p k snk  = let b' = map (\(i,ki) -> if ki == 0 then -infty else fk+ sn ! ki A.! i) (zip [1..] k)
                         bp = snd $ head $ sortBy (\(ki,xi) (kj,xj) -> compare (xj A.! p)  (xi A.! p)) (assocs snk)
                     in if Data.Map.Lazy.null snk then b' ++ [-infty] else b' ++ [bp A.! p + fk]
                       
-- Resoud le probleme P^b.
getNewPoint :: [Var] ->
               [Double] ->
               LPT Var Double (VSupplyT (WriterT LaTeX IO)) (Maybe [Double])
getNewPoint objs b = do                       
  s <- get
  foldM (\_ (ck,bk) -> varSum [ck] `geqTo` bk) () $ zip objs b
  (ret,ans) <- glpSolve mipDefaults{msgLev=MsgErr}
  put s
  case ret of 
    Success -> let sol = map (snd (fromJust ans) !) objs
               in if and $ map (== 0) sol
                  then return Nothing
                  else return $ Just (map (snd (fromJust ans) !) objs)
    otherwise -> return $ Nothing
    
{-Algorithme général :                       
 (Init : générer une solution ND)
 On dispose de Sn (solutions déjà trouvées).
   (1) : On génère l'ensemble des vecteurs k et les bornes associées
   (2) : On résoud les problèmes associés sur chacune des bornes
   (3) : On considère la meilleure solution sur le p-eme critère
-}

x /\ y = and $ zipWith (>=) x y

lokKok' objs arch sn p n = let kset = buildK sn (p - 2)
                               bset = map (\(snk,k) -> buildB sn (p - 1) k snk) kset
                           in do
                             archives <- foldM (\l b -> let 
                                                     b' = [bi | (zi,bi) <- l, bi /\ b, zi == Nothing] ++ [bi | (zi,bi) <- arch, b /\ bi, zi == Nothing]
                                                     b'' = [zi | (zi,bi) <- l, b /\ bi, isJust zi, fromJust zi /\ b] ++ [zi | (zi,bi) <- arch, b /\ bi, isJust zi, fromJust zi /\ b]
                                                 in do
                                                   zb <- if Data.List.null b' && Data.List.null b'' 
                                                         then do 
                                                           ans <-  getNewPoint objs b
                                                           lift $ tell $ latexDumpSubModelresult n b True $ if isJust ans then fromJust ans else []
                                                           trace (dumpSubModelResult n b True $ if isJust ans then fromJust ans else []) return ans
                                                         else if Data.List.null b'
                                                              then do 
                                                                lift $ tell $latexDumpSubModelresult n b False []
                                                                trace (dumpSubModelResult n b False "Useless to solve.") $ return $  head b''
                                                              else do 
                                                                lift $ tell $ latexDumpSubModelresult n b False []
                                                                trace (dumpSubModelResult n b False "Infeasible" ) $ return $ Nothing
                                                   return ((zb,b):l)) [] bset
                             let ans = [A.array (1,p) $ zip [1..] (fromJust zb) | (zb,_) <- archives, isJust zb]
                                 zstar = head $ sortBy (\x y -> compare (y A.! p) (x A.! p) ) ans
                               in if Data.List.null ans
                                  then trace ("No more poins found.") return sn
                                  else do
                                    lift $ tell $ latexDumpModelResult n zstar   
                                    trace (dumpModelResult n zstar) lokKok' objs (archives ++ arch) (Data.Map.Lazy.insert (n+1) zstar sn) p (n+1)
                      
lokKok domain p = do
  objs <- domain
  
  x <- getNewPoint objs (repeat (-infty))
  case x of
    Nothing -> error "Empty ND set"
    Just v -> do 
      lift $ tell $ textbf "model" & textbf "b" & textbf "solve?" & textbf "local ND point" & textbf "new ND point" <> lnbk <> hline <> lnbk
      lift $ tell $ latexDumpSubModelresult  0 (take (fromIntegral $ p-1) (repeat $ -infty))  (True)  v
      lift $ tell $ latexDumpModelResult 0 (A.array (1,p) $ zip [1..] v)
      trace ("model\tb\t\tsolve\t\tlocal ND point\t\tnew ND point\n" ++
             dumpSubModelResult 0 (take (fromIntegral $ p-1) (repeat $ -infty) ) True x ++ "\n" ++
             dumpModelResult 0 (A.array (1,p) $ zip [1..] v))
        lokKok' objs [] (insert 1 (A.array (1,p) $ zip [1..] v) empty) p 1
    

dumpSubModelResult n b explorep zb = show n ++ "\t" ++ show b ++ "\t"  ++ show explorep ++ "\t" ++ show zb 
dumpModelResult n ans = show n ++ "\t\t\t\t\t\t\t\t" ++ show (A.elems ans)

latexDumpSubModelresult n b explorep zb = (fromString $ show n) & (vector b) & (fromString $ show explorep) & (vector zb) <> lnbk
latexDumpModelResult n ans = fromString (show n) & "" & "" & "" & (vector $ A.elems ans) <> lnbk