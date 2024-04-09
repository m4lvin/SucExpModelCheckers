{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module SucModelChecker where

import Data.Set (Set)
import qualified Data.Set as Set

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Map (Map, (!))
import qualified Data.Map as Map

import SMCDEL.Language
import SMCDEL.Internal.Help (powerset)

-- | Syntax of mental programs.
-- π ::= p <- β | β? | π ; π | π ∪ π | π ∩ π) | π⁻
data MenProg = Ass Prp Form            -- Assign prop to truthvalue of form
             | Tst Form                -- Test form
             | Seq [MenProg]           -- Execute forms sequencially
             | Cup [MenProg]           -- execute either of the forms
             | Cap [MenProg]           -- intersection of forms
             | Inv MenProg             -- inverse of form
             deriving (Show, Eq, Ord)

-- | A state is the set of propositions that are true.
type State = IntSet

-- a Succinct representation of a model
-- third parameter [Form]: announced formulas, listed with the newest announcement first
data SuccinctModel = SMo [Prp] Form [Form] (Map Agent MenProg) deriving (Eq,Ord,Show)

instance HasVocab SuccinctModel where
  vocabOf (SMo v _ _ _) = v

instance HasAgents SuccinctModel where
  agentsOf (SMo _ _ _ rel) = Map.keys rel

statesOf :: SuccinctModel -> Set State
statesOf (SMo vocab betaM []     _) = Set.filter (`boolIsTrue` betaM) (allStatesFor vocab)
statesOf (SMo vocab betaM (f:fs) rel) = Set.filter (\s -> sucIsTrue (oldModel,s) f) (statesOf oldModel) where
  oldModel = SMo vocab betaM fs rel

-- | Given a state, evaluate a Boolean formula.
boolIsTrue :: State -> Form -> Bool
boolIsTrue _  Top         = True
boolIsTrue _  Bot         = False
boolIsTrue s (PrpF (P i)) = i `IntSet.member` s
boolIsTrue a (Neg f)      = not $ boolIsTrue a f
boolIsTrue a (Conj fs)    = all (boolIsTrue a) fs
boolIsTrue a (Disj fs)    = any (boolIsTrue a) fs
boolIsTrue a (Impl f g)   = not (boolIsTrue a f) || boolIsTrue a g
boolIsTrue a (Equi f g)   = boolIsTrue a f == boolIsTrue a g
boolIsTrue _ (Xor _)      = error "not implemented by this system"
boolIsTrue _ (Forall _ _) = error "not implemented by this system"
boolIsTrue _ (Exists _ _) = error "not implemented by this system"
boolIsTrue _ (K _ _)           = error "not a boolean formula"
boolIsTrue _ (Kw _ _)          = error "not a boolean formula"
boolIsTrue _ (Ck _ _)          = error "not a boolean formula"
boolIsTrue _ (Ckw _ _)         = error "not a boolean formula"
boolIsTrue _ (Dk _ _)          = error "not a boolean formula"
boolIsTrue _ (Dkw _ _)         = error "not a boolean formula"
boolIsTrue _ (PubAnnounce {})  = error "not a boolean formula"
boolIsTrue _ (PubAnnounceW {}) = error "not a boolean formula"
boolIsTrue _ (Announce {})     = error "not a boolean formula"
boolIsTrue _ (AnnounceW {})    = error "not a boolean formula"
boolIsTrue _ (Dia _ _)         = error "not a boolean formula"

-- | The set of all states for a given vocabulary.
allStatesFor :: [Prp] -> Set State
allStatesFor = Set.map IntSet.fromList . Set.fromList . map (map (\(P i) -> i)) . powerset

-- | Check if the state is in a model, also after the already happened announcements!
isStateOf :: State -> SuccinctModel -> Bool
isStateOf s (SMo _     betaM []     _  ) = s `boolIsTrue` betaM
isStateOf s (SMo vocab betaM (f:fs) rel) =
   sucIsTrue (oldModel,s) f && (s `isStateOf` oldModel) where
     oldModel = SMo vocab betaM fs rel

-- whether a state is reachable from another state (first argument is full vocabulary)
areConnected :: [Prp] -> MenProg -> State -> State -> Bool
areConnected _ (Ass (P i) f) s1 s2       = if boolIsTrue s1 f
                                         then IntSet.insert i s1 == s2
                                         else IntSet.delete i s1 == s2
areConnected _ (Tst f) s1 s2         = s1 == s2 && boolIsTrue s1 f
areConnected _ (Seq []       ) s1 s2 = s1 == s2
areConnected v (Seq (mp:rest)) s1 s2 = any (\ s3 -> areConnected v (Seq rest) s3 s2) (reachableFromHere v mp s1)
areConnected _ (Cup []       ) _ _   = False
areConnected v (Cup (mp:rest)) s1 s2 = areConnected v mp s1 s2 || areConnected v (Cup rest) s1 s2
areConnected _ (Cap []       ) _ _   = True
areConnected v (Cap (mp:rest)) s1 s2 = areConnected v mp s1 s2 && areConnected v (Cap rest) s1 s2
areConnected v (Inv mp       ) s1 s2 = areConnected v mp s2 s1

-- returns all states that are reachable from a certain state in a mental program
-- (first argument is full vocabulary)
reachableFromHere :: [Prp] -> MenProg -> State -> Set State
reachableFromHere _ (Ass (P i) f) s = if boolIsTrue s f
                                     then Set.singleton $ IntSet.insert i s
                                     else Set.singleton $ IntSet.delete i s
reachableFromHere _ (Tst f) s         = if boolIsTrue s f then Set.singleton s else Set.empty
reachableFromHere _ (Seq []) s        = Set.singleton s
reachableFromHere v (Seq (mp:rest)) s = Set.unions $ Set.map (reachableFromHere v (Seq rest)) (reachableFromHere v mp s)
reachableFromHere _ (Cup []) _        = Set.empty
reachableFromHere v (Cup (mp:rest)) s = reachableFromHere v mp s `Set.union` reachableFromHere v (Cup rest) s
reachableFromHere _ (Cap []) _        = Set.empty
reachableFromHere v (Cap (mp:rest)) s = reachableFromHere v (Cap rest) s `Set.intersection` reachableFromHere v mp s
reachableFromHere v (Inv mp)        s = Set.filter (\s' -> areConnected v mp s' s) (allStatesFor v)

-- isTrue for succinct models
sucIsTrue :: (SuccinctModel, State) -> Form -> Bool
sucIsTrue _  Top       = True
sucIsTrue _  Bot       = False
sucIsTrue (_ ,s) (PrpF (P i)) = i `IntSet.member` s
sucIsTrue a (Neg f)    = not $ sucIsTrue a f
sucIsTrue a (Conj fs)   = all (sucIsTrue a) fs
sucIsTrue a (Disj fs)   = any (sucIsTrue a) fs
sucIsTrue a (Impl f g)  = not (sucIsTrue a f) || sucIsTrue a g
sucIsTrue a (Equi f g)  = sucIsTrue a f == sucIsTrue a g
sucIsTrue (m@(SMo v _ _ rel), s) (K i f) =
   all
    (\s' -> sucIsTrue (m,s') f)
    (Set.filter (`isStateOf` m) $ reachableFromHere v (rel ! i) s)
sucIsTrue a (Kw i f) = sucIsTrue a (Disj [ K i f, K i (Neg f) ])
sucIsTrue (m, s) (PubAnnounce f g)  = not (sucIsTrue (m, s) f) || sucIsTrue(m `update` f, s) g
sucIsTrue _ (Xor _) = error "not implemented by this system"
sucIsTrue _ (Forall _ _) = error "not implemented by this system"
sucIsTrue _ (Exists _ _) = error "not implemented by this system"
sucIsTrue _ (Ck _ _) = error "not implemented by this system"
sucIsTrue _ (Ckw _ _) = error "not implemented by this system"
sucIsTrue _ (PubAnnounceW _ _) = error "not implemented by this system"
sucIsTrue _ (Announce {}) = error "not implemented by this system"
sucIsTrue _ (AnnounceW {}) = error "not implemented by this system"
sucIsTrue _ (Dia _ _) = error "not implemented by this system"
sucIsTrue _ (Dk _ _) = error "not implemented by this system"
sucIsTrue _ (Dkw _ _) = error "not implemented by this system"

instance Pointed SuccinctModel State
type PointedSuccinctModel = (SuccinctModel, State)

instance Semantics PointedSuccinctModel where
  isTrue = sucIsTrue

instance Semantics SuccinctModel where
  isTrue m f = all (\s -> isTrue (m,s) f) (statesOf m)

-- | Update a succinct model with a public announcent.
sucPublicAnnounce :: SuccinctModel -> Form -> SuccinctModel
sucPublicAnnounce (SMo v fm fs rel) f = SMo v fm (f:fs) rel

instance Update PointedSuccinctModel Form where
   checks = []
   unsafeUpdate (m, s) f = (sucPublicAnnounce m f, s)

instance Update SuccinctModel Form where
   checks = []
   unsafeUpdate = sucPublicAnnounce
