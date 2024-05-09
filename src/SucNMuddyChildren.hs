module SucNMuddyChildren where

import qualified Data.Map as Map

import SucModelChecker
import NMuddyChildren
import Translator

import SMCDEL.Language hiding(isTrue, (|=))

-- n children of which the first m are muddy
-- a bit of a shortcut but way more efficient
sucMuddyModelFor :: Int -> Int -> PointedSuccinctModel
sucMuddyModelFor n m = (SMo [(P 0) .. (P (n-1))] Top [] (Map.fromList $ makeSucRels n), toState [(P 0) .. (P (m-1))])

-- n children, of which m are muddy
-- returns with a list of all possible actual states
sucMuddyModelsFor :: Int -> Int -> (SuccinctModel,[State])
sucMuddyModelsFor n m = (SMo voc Top [] (Map.fromList $ makeSucRels n), makeStates voc m) where
  voc = [(P 0) .. (P (n-1))]

-- makes n children and their relations
makeSucRels :: Int -> [ (Agent, MenProg) ]
makeSucRels n = [ ("child" ++ show k, Cup [Ass (P k) Top, Ass (P k) Bot]) | k <- [0 .. (n - 1)]]

-- makes all viable states of n children in which m are muddy
makeStates :: [Prp] -> Int -> [State]
makeStates vocabulary m = [toState k | k <- powerList vocabulary, length k == m]

-- finds the number of announcements necessary for the muddy children to know their own muddiness
sucFindMuddyNumber :: Int -> (SuccinctModel,State) -> Int
sucFindMuddyNumber n (sucMod, s) = loop sucMod where
 loop newSucMod = if sucIsTrue (newSucMod, s) (somebodyKnows n)
                  then 0
                  else loop (sucPublicAnnounce newSucMod (nobodyKnows n)) + 1

sucMoutofN :: Int -> Int -> Int
sucMoutofN m n = sucFindMuddyNumber n (sucMuddyModelFor n m)

-- checks the number of children for the function muddyModelFor
sucCheck :: Int -> Int -> Bool
sucCheck n m = sucFindMuddyNumber n (sucMuddyModelFor n m) == m
