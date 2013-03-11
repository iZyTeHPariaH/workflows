import Algorithms.Lokman hiding (infty)
import Control.Monad
import Data.Monoid
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.LPMonad
import Control.Monad.LPMonad.Supply
import Data.Map.Lazy hiding (map,null,foldl,member)
import Data.LinearProgram.Common
import Data.Algebra
import qualified Data.Array as A

import Data.Maybe
import Data.LinearProgram.GLPK.Solver
import Debug.Trace

trace' x = trace $ "[*] " ++ show x

data Task = Task {taskId :: Integer, 
                            taskDependancies :: [Integer],
                            taskSuccessors :: [Integer]} deriving (Eq,Ord,Show) 
data Workflow = Workflow {graph :: A.Array Integer Task,
                          arcs :: Map (Integer,Integer) Bool,
                          durations :: A.Array (Integer,Integer) Double,
                          outputs :: A.Array (Integer,Integer,Integer) Double,
                          applicationCost :: A.Array (Integer,Integer) Double,
                          applicationOutputCosts :: A.Array (Integer,Integer,Integer) Double}
infty = 900
                                        
lp w = do
    let n = fromIntegral $ snd $ A.bounds $ graph w 
        m = fromIntegral $ snd $ snd $ A.bounds $ durations w -- les machines sont les colonnes
    [max,cost] <- supplyN 2
    (x,y) <- foldM (\(xi,yi) i -> do
                              xk <- supplyN $ fromIntegral m 
                              yk <- supplyN $ fromIntegral m
                              foldM (\_ e -> setVarKind e BinVar) () yk
                              return (insert i (A.listArray (1,m) xk) xi, 
                                        insert i (A.listArray (1,m) yk) yi) ) 
                        (empty,empty) 
                        (map taskId $ A.elems $ graph w)
  
    (alphas,z) <- foldM (\(acc,acc') (i,j) -> do
                        if isJust (Data.Map.Lazy.lookup (i,j) (arcs w)) 
                           then do 
                               z' <- genDependancies w i j (fromIntegral m) x y acc' 
                               return (acc,z')
                        else if isJust (Data.Map.Lazy.lookup (j,i) (arcs w) ) 
                           then do
                               z' <- genDependancies w j i (fromIntegral m) x y acc'
                               return (acc,z')
                        else do
                            tmp <- runCont (boundedP i j (graph w)) return
                            if tmp then return (acc,acc')
                            else do 
                               al' <- genNonDependancies w i j m x y acc
                               return (al',acc')) (empty,empty) [(taskId ti, taskId tj) | ti <- A.elems $ graph w, tj <- A.elems $ graph w, taskId ti < taskId tj]
    -- Liens entre les yi et les xi   
    foldM (\_ (i,k) -> linCombination [(1,(y ! i) A.! k)] `geq` linCombination [(1/infty, (x ! i ) A.! k)] >> 
                       linCombination [(infty, (x ! i) A.! k) ] `geq` linCombination [(1,y ! i A.! k)]) 
          ()  [(i,k) | i <- [1..n], k <- [1..m]] 
      
    foldM (\_ i -> linCombination [(1,y ! i A.! k) | k <- [1..m]] `equalTo` 1) () [1..n]
         
   -- Contraintes de maximum
    foldM (\_ i -> dateFin w i m x y max) () ( map taskId $ A.elems $ graph w)
    
    -- Max (-max) = Min max
    setObjective $ linCombination [(-1,max),(-1/10000, cost)] 
    setDirection Max
    [max',cost'] <- supplyN 2
    varSum [cost'] `equal` linCombination [(-1,cost)]
    varSum [max'] `equal` linCombination [(-1,max)]
    linCombination (costCombination w y z m) `equal` linCombination [(1,cost)]
    
   -- linCombination [(1,cost)] `leqTo` 3000
    
    
  
    
    writeLPToFile "test.lp"
    return [cost',max']
genDependancies w i j m x y zmap =  do
             let yi = y ! i
                 yj = y ! j
             z <-  foldM (\a (k,l) -> do
                                     zijkl <- supplyNew
                                     setVarKind zijkl BinVar
                                     return $ insert (i,j,k,l) zijkl a) zmap [(k,l) | k <- [1..m], l <- [1..m]]
            
             foldM (\_ (k,l) -> do 
                     -- zijkl - yik - yjl >= -1
                     -- yik =1 et yjl = 1 => zijkl = 1
                     linCombination [(1,z ! (i,j,k,l)), (-1, yi A.! k), (-1, yj A.! l)] `geqTo` (-1)  
               
                     -- zijkl = 1 => yik = 1 et yjl = 1
                     -- yjl + yik >= -M ( 1 - zijkl) + 2*zijkl
                     -- yjl + yik >= - M  + zijkl(M + 2)
                     linCombination [(1,yj A.! l),(1,yi A.! k),(-infty - 2, z ! (i,j,k,l) )] `geqTo` (-infty)
                     )
               () 
               [(k,l) | k <- [1..m], l <- [1..m]]
             linCombination                                                               
               (zip  (repeat 1) (A.elems (x ! i)) ++                           
                zip [durations w A.! (i,k) | k <- [1..m] ]  (A.elems (y ! i)) ++ 
                [(outputs w A.! (i,k,l) , z ! (i,j,k,l)) | k <- [1..m], l <- [1..m]] ) 
               `leq` linCombination ( zip (repeat 1) (A.elems (x ! j))) 
             return z
                               
genNonDependancies w i j m x y alphamap =
  foldM (\acc k -> do
    [alphaij, alphaji] <- supplyN 2
    setVarKind alphaij BinVar
    setVarKind alphaji BinVar
    linCombination [(1,((x ! i) A.!  k)),(-1, (x ! j) A.! k),(infty,alphaij)]  `leqTo` (infty - (durations w A.! (i,k)))
    linCombination [(1,((x ! j) A.!  k)),(-1, (x ! i) A.! k),(infty,alphaji)]  `leqTo` (infty - (durations w A.! (j,k)))
    
    -- yik = 1 et yjk = 1 => aij = 1 ou aji = 1
    -- linCombination [(1,a),(1,b),(-1, y ! 2 A.! 1), (-1, y ! 3 A.! 1)] `geqTo` (-1)
    --linCombination [(1, (y ! i) A.! k), (1,(y ! j) A.! k), (-1, alphaij), (-1,alphaji) ] `leqTo` 1
    linCombination [(-1,alphaij),(-1,alphaji),(1,y ! i A.! k),(1, y ! j A.! k)] `leqTo` (1)
    -- aij = 1 ou aji = 1 => yik = 1 et yjk = 1
    
    
    let yik = y ! i A.! k
        yjk = y ! j A.! k
    linCombination [(-1,alphaij),(1,yik)] `geqTo` 0
    linCombination [(-1,alphaij),(1,yjk)]  `geqTo` 0
    linCombination [(-1,alphaji),(1,yik)] `geqTo` 0
    linCombination [(-1,alphaji),(1,yjk)] `geqTo` 0 
    
    linCombination [(1,alphaij),(1,alphaji)] `leqTo` 1
    
    return $ Data.Map.Lazy.insert (i,j,k) alphaij $ insert (j,i,k) alphaji acc 
    )
         alphamap
         [1..m]

dateFin w i m x y mu = linCombination ([(1,(x ! i) A.! k) | k <- [1..m]] ++ [(durations w A.! (i,k),(y ! i) A.! k ) | k <- [1..m] ]) `leq` linCombination [(1,mu)]                                


testW' wf = do
  (x,lpt) <- runVSupplyT $ runLPT $ lp wf
  return x
  
readMatrix :: String -> Integer -> Integer -> IO (A.Array (Integer,Integer) Double)
readMatrix fname n m = do
  file <- readFile fname
  let lignes = zip [1..]  (  map (\l -> zip [1..] (words l)) $ lines file) 
  return $ A.array ((1,1),(n,m)) [((i,j),read w) | (i,l) <- lignes,
                                                    i <= n,
                                                    (j,w) <- l, 
                                                    j <= m]
                       
computeOutputs aa rr n m op = A.array ((1,1,1),(n,m,m)) $ 
                            [((i,k,l),if bp > 0 then v `op` bp else 0 )| i <- [1..n], 
                             let val =  [aa A.! (i,i') | i' <- [1..n], aa A.! (i,i') > 0]
                                 v = if null val then 0 else head val, 
                             k <- [1..m],
                             l <- [1..m],
                             let bp = rr A.! (k,l)]
    
getGraph matrix n m =       
      foldl (\a ((i,j),v) -> if v > 0 then (insert (i,j) True a )
                             else a  ) empty (A.assocs matrix)
          
          

buildWF appliAppli ressRess appliRessTime ressRessCost appliRessCost n m = do                                                                                                                                                                                    
    aa <- (readMatrix appliAppli n n)
    rr <- readMatrix ressRess m m
    art <- readMatrix appliRessTime n m
    
    rrc <- readMatrix ressRessCost m m
    arc <- readMatrix appliRessCost n m
    
    let gr = getGraph aa n m
        taches = A.array (1,n) $ map (\i -> (i,Task i  [] []))  [1..n]
        taches'  = foldl (\t (i,j) -> let ti = t A.! i
                                          tj = t A.! j
                                          ti' = ti{taskSuccessors = j:taskSuccessors ti}
                                          tj' = tj{taskDependancies = i:taskDependancies tj} in
                                      t A.// [(i,ti'),(j,tj')]  )  
                            taches  (map fst $ toList gr)
        outputs = computeOutputs aa rr n m (/)
        outputsCosts = computeOutputs aa rrc n m (*)
        
    putStrLn "Taches : " 
    putStrLn $ unlines $ map show (A.elems taches')
    
    putStrLn "Application Ressource Time : "
    putStrLn $ showMatrix art
    
    putStrLn "Application Application : "
    putStrLn $ showMatrix aa
    
    putStrLn "Ressources Ressources : "
    putStrLn $ showMatrix rr
 
    return $ Workflow taches' gr art outputs arc outputsCosts

test = do 
  wf <- (buildWF "heft3/aa.txt" "heft3/rr.txt" "heft3/art.txt" "heft3/rrc.txt" "heft3/arc.txt" 10 3)
  (ans,_) <- runVSupplyT $ runLPT $ lokKok (lp wf) 2
  putStrLn $ unlines $ map (show.A.elems) (elems ans)
showMatrix m = let (_,(n,p)) = A.bounds m in
  unlines $ map (\l -> unwords $ [show $ m A.! (l,j) | j <- [1..p]]) [1..n]
  
search point graphe current voisins =  if point `elem` voisins current
                                       then return True
                                       else do 
                                         let nxt = map (graphe A.!) (voisins current)
                                         foldM (\acc e -> search point graphe e voisins >>= \a -> return $ acc || a) False nxt 
                                         
boundedP i j graphe = let tj = graphe A.! j
                      in do	
                        x <- search i graphe tj taskSuccessors
                        y <- search i graphe tj taskDependancies
                        return $ x || y                                         
                                         
tacheMachine w y z m ti k = 
    let i = taskId ti in 
    [(applicationCost w A.! (i,k) , y ! i A.! k)] ++ 
    [ (applicationOutputCosts w A.! (i,k,l), z ! (i,j,k,l) )  | j <- taskSuccessors ti, k <- [1..m], l <- [1..m] ]  
      
costCombination w y z m = do
  foldl (\a (i,k) -> a ++ tacheMachine w y z m (graph w A.! i) k) [] 
    [(i,k) | i <- map (taskId) $ A.elems (graph w), k <- [1..m]]
                                                    
                                                    
                                         
                                         
                                         
                                         
                                         
                                                 
