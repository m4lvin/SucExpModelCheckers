-- Based on https://github.com/jrclogic/SMCDEL/blob/master/bench/muddychildren.hs
-- Modified for the explicit and succinct model checkers defined here.

module Main (main) where

import Criterion.Main

import qualified SMCDEL.Explicit.DEMO_S5 as DEMO_S5

import SucNMuddyChildren
import NMuddyChildren
import Translator

mudDemoKrpInit :: Int -> Int -> DEMO_S5.EpistM [Bool]
mudDemoKrpInit n m = DEMO_S5.Mo states agents [] rels points where
  states = DEMO_S5.bTables n
  agents = map DEMO_S5.Ag [1..n]
  rels = [(DEMO_S5.Ag i, [[tab1++[True]++tab2,tab1++[False]++tab2] |
                   tab1 <- DEMO_S5.bTables (i-1),
                   tab2 <- DEMO_S5.bTables (n-i) ]) | i <- [1..n] ]
  points = [replicate (n-m) False ++ replicate m True]

findNumberDemoS5 :: Int -> Int -> Int
findNumberDemoS5 n m = findNumberDemoLoop n m 0 start where
  start = DEMO_S5.updPa (mudDemoKrpInit n m) (DEMO_S5.fatherN n)

findNumberDemoLoop :: Int -> Int -> Int -> DEMO_S5.EpistM [Bool] -> Int
findNumberDemoLoop n m count curMod =
  if DEMO_S5.isTrue curMod (DEMO_S5.dont n)
    then findNumberDemoLoop n m (count+1) (DEMO_S5.updPa curMod (DEMO_S5.dont n))
    else count

findNumberExplicit :: Int -> Int -> Int
findNumberExplicit n m = findMuddyNumber n (muddyModelFor n m )

findNumberSuccinct :: Int -> Int -> Int
findNumberSuccinct n m = sucFindMuddyNumber n (sucMuddyModelFor n m )

findNumberTranslatedExplicit :: Int -> Int -> Int
findNumberTranslatedExplicit n m = findMuddyNumber n (suc2exp (sucMuddyModelFor n m) )

findNumberTranslatedSuccinct :: Int -> Int -> Int
findNumberTranslatedSuccinct n m = sucFindMuddyNumber n (exp2suc (muddyModelFor n m) )

main :: IO ()
main = defaultMain (map mybench
  [ ("DEMOS5"    , findNumberDemoS5    , [3..9] )
  , ("Explicit"  , findNumberExplicit  , [3..10] )
  , ("Succinct"  , findNumberSuccinct  , [3..15]  )
  , ("TransExp"  , findNumberTranslatedExplicit  , [3..6]  )
  , ("TransSuc"  , findNumberTranslatedSuccinct  , [3..5]  )
  ])
  where
    mybench (name,f,range) = bgroup name $ map (run f) range
    run f k = bench (show k) $ whnf (\n -> f n n == n-1) k -- NOTE: n-1 is the correct answer
