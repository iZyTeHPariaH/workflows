{-#LANGUAGE OverloadedStrings #-}
module Logs.Logs where

import Control.Monad.Writer
import Text.LaTeX
import Text.LaTeX.Packages.Inputenc
import Text.LaTeX.Packages.AMSMath 

buildReport :: LaTeX -> LaTeX -> LaTeX
buildReport t ans  = documentclass [] article <> 
                     usepackage [utf8] inputenc <>
                     usepackage [] amsmath <>
                     title ("Résultats de l'optimisation") <>
                     document( section "Frontière trouvée" <>
                               tabular Nothing [VerticalLine,LeftColumn,
                                                VerticalLine,LeftColumn,
                                                VerticalLine] ans <>
                               section "Résultats" <> 
                               tabular Nothing [VerticalLine,LeftColumn, 
                                                VerticalLine,  LeftColumn,
                                                VerticalLine,LeftColumn,
                                                VerticalLine,LeftColumn,
                                                VerticalLine,LeftColumn,
                                                VerticalLine] t)
                     
vector :: [Double] -> LaTeX
vector v = if null v then""
           else math $ raw "\\left[\\begin{array}{c}" <>
                  foldl (\a e -> a <> lnbk <> fromString (show e)) (fromString $ show $ head v) (tail v) <>
                  raw "\\end{array}\\right]"    