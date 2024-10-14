{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{- |

This module implements so-called /Succinct Models/ where the relations of agents
are encoded using /Mental Programs/, a variant of /Propositional Dynamic Logic/.

References:

- [CS 2017]
  Tristan Charrier and François Schwarzentruber:
  /A Succinct Language for Dynamic Epistemic Logic/.
  In: AAMAS 2017.
  <http://www.aamas2017.org/proceedings/pdfs/p123.pdf>

- [G 2020]
  Malvin Gattinger: /Towards Symbolic and Succinct Perspective Shifts/.
  In: EpiP at ICAPS 2020.
  Paper: <https://doi.org/10.5281/zenodo.4767546>
  Video: <https://www.youtube-nocookie.com/embed/h-LFXeqXKf4?recommends=0>
-}

module SucModelChecker where

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Test.QuickCheck

import SMCDEL.Language
import SMCDEL.Internal.Help (powerset)

-- | Syntax of mental programs.
-- π ::= p <- β | β? | π ; π | π ∪ π | π ∩ π) | π⁻
data MenProg = Ass Prp Form            -- ^ assign value of form to prop (can be restricted to Top/Bot)
             | Tst Form                -- ^ test form
             | Seq [MenProg]           -- ^ sequence
             | Cup [MenProg]           -- ^ union aka choice
             | Cap [MenProg]           -- ^ intersection
             | Inv MenProg             -- ^ inverse of program (can be eliminated)
             deriving (Show, Eq, Ord)

-- | Remove operators for inverse and general assignment.
-- See Lemma 19 in [Gat 2020]
removeOps :: MenProg -> MenProg
removeOps mp@(Ass _ Top) = mp
removeOps mp@(Ass _ Bot) = mp
removeOps    (Ass prp f) = Cup [ Seq [Tst f, Ass prp Top]
                               , Seq [Tst (Neg f), Ass prp Bot] ]
removeOps (Tst tf      ) = Tst tf
removeOps (Seq mps     ) = Seq $ map removeOps mps
removeOps (Cup mps     ) = Cup $ map removeOps mps
removeOps (Cap mps     ) = Cap $ map removeOps mps
removeOps (Inv mp) = case removeOps mp of
  Ass p Top -> Seq [ Tst (PrpF p), Cup [Ass p Top, Ass p Bot] ]
  Ass p Bot -> Seq [ Tst (Neg $ PrpF p), Cup [Ass p Top, Ass p Bot] ]
  Ass _ _ -> error "impossible"
  Tst tf -> Tst tf
  Seq mps -> Seq (reverse $ map (removeOps . Inv) mps)
  Cup mps -> Cup (map (removeOps . Inv) mps)
  Cap mps -> Cap (map (removeOps . Inv) mps)
  Inv _ -> error "impossible"

-- | A state is the set of propositions that are true.
type State = IntSet

-- a Succinct representation of a model
-- third parameter [Form]: announced formulas, listed with the newest announcement first
data SuccinctModel = SMo [Prp] Form [Form] (Map Agent MenProg) deriving (Eq,Ord,Show)

instance HasVocab SuccinctModel where
  vocabOf (SMo v _ _ _) = v

instance HasAgents SuccinctModel where
  agentsOf (SMo _ _ _ mp) = Map.keys mp

-- | States of a succinct model -- after restricting due to the announcements made.
statesOf :: SuccinctModel -> Set State
statesOf (SMo vocab betaM []     _) = Set.filter (`boolIsTrue` betaM) (allStatesFor vocab)
statesOf (SMo vocab betaM (f:fs) mp) = Set.filter (\s -> sucIsTrue (oldModel,s) f) (statesOf oldModel) where
  oldModel = SMo vocab betaM fs mp

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
boolIsTrue a (Xor fs)     = odd $ length (filter id $ map (boolIsTrue a) fs)
boolIsTrue a (Forall [] f) = boolIsTrue a f
boolIsTrue a (Forall (P p:ps) f) = let nf = Forall ps f
                                   in boolIsTrue (IntSet.insert p a) nf && boolIsTrue (IntSet.delete p a) nf
boolIsTrue a (Exists [] f) = boolIsTrue a f
boolIsTrue a (Exists (P p:ps) f) = let nf = Forall ps f
                                   in boolIsTrue (IntSet.insert p a) nf || boolIsTrue (IntSet.delete p a) nf
boolIsTrue _ (K _ _)           = error "not a boolean formula"
boolIsTrue _ (Kw _ _)          = error "not a boolean formula"
boolIsTrue _ (Ck _ _)          = error "not a boolean formula"
boolIsTrue _ (Ckw _ _)         = error "not a boolean formula"
boolIsTrue _ (Dk _ _)          = error "not a boolean formula"
boolIsTrue _ (Dkw _ _)         = error "not a boolean formula"
boolIsTrue _ (G _)             = error "not a boolean formula"
boolIsTrue _ (PubAnnounce {})  = error "not a boolean formula"
boolIsTrue _ (Dia _ _)         = error "not a boolean formula"
-- boolIsTrue a f = boolEvalViaBdd (map P $ IntSet.toList a) f -- alternative

-- | The set of all states for a given vocabulary.
-- This can be exponential and should be avoided.
allStatesFor :: [Prp] -> Set State
allStatesFor = Set.map IntSet.fromList . Set.fromList . map (map (\(P i) -> i)) . powerset

-- | Check if the state is in a model, also after the already happened announcements!
isStateOf :: State -> SuccinctModel -> Bool
isStateOf s (SMo _     betaM []     _  ) = s `boolIsTrue` betaM
isStateOf s (SMo vocab betaM (f:fs) mp) =
   sucIsTrue (oldModel,s) f && (s `isStateOf` oldModel) where
     oldModel = SMo vocab betaM fs mp

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
reachableFromHere v (Inv mp)        s = Set.filter (\s' -> areConnected v mp s' s) (allStatesFor v) -- TODO replace this

-- | Semantics on succinct models, computed explicitly.
sucIsTrue :: (SuccinctModel, State) -> Form -> Bool
sucIsTrue _  Top       = True
sucIsTrue _  Bot       = False
sucIsTrue (_ ,s) (PrpF (P i)) = i `IntSet.member` s
sucIsTrue a (Neg f)    = not $ sucIsTrue a f
sucIsTrue a (Conj fs)   = all (sucIsTrue a) fs
sucIsTrue a (Disj fs)   = any (sucIsTrue a) fs
sucIsTrue a (Xor fs)    = odd $ length (filter id $ map (sucIsTrue a) fs)
sucIsTrue a (Impl f g)  = not (sucIsTrue a f) || sucIsTrue a g
sucIsTrue a (Equi f g)  = sucIsTrue a f == sucIsTrue a g
sucIsTrue (m@(SMo v _ _ mp), s) (K i f) =
   all
    (\s' -> sucIsTrue (m,s') f)
    (Set.filter (`isStateOf` m) $ reachableFromHere v (mp ! i) s)
sucIsTrue a (Kw i f) = sucIsTrue a (Disj [ K i f, K i (Neg f) ])
sucIsTrue (m, s) (PubAnnounce f g)  = not (sucIsTrue (m, s) f) || sucIsTrue (m `update` f, s) g
sucIsTrue _ f = error $ "Operator not implemented: " ++ show f

-- | Push box of a mental program into a Boolean formula.
push :: MenProg -> Form -> Form
push (Ass (P i) af) (PrpF (P j)) = if i == j then af else PrpF (P j)
push (Ass (P _) _ ) Top = Top
push (Ass (P _) _ ) Bot = Bot
push (Ass (P i) af) (Neg f) = Neg $ push (Ass (P i) af) f
push (Ass (P i) af) (Conj fs) = Conj $ map (push (Ass (P i) af)) fs
push (Ass (P i) af) (Disj fs) = Disj $ map (push (Ass (P i) af)) fs
push (Ass (P i) af) (Xor fs) = Xor $ map (push (Ass (P i) af)) fs
push (Ass (P i) af) (Impl f g) = Impl (push (Ass (P i) af) f) (push (Ass (P i) af) g)
push (Ass (P i) af) (Equi f g) = Equi (push (Ass (P i) af) f) (push (Ass (P i) af) g)
push (Tst tf)        f = tf `Impl` f
push (Seq []       ) f = f
push (Seq (mp:rest)) f = push mp $ push (Seq rest) f
push (Cup mps      ) f = Conj [ push mp f | mp <- mps ]
push (Cap _        ) _ = error "TODO" -- Conj [ push mp f | mp <- mps ] -- PROBLEM - how to do this?
push (Inv mp       ) f = push (removeOps (Inv mp)) f
push _ f = error $ "not a Boolean formula: " ++ show f

-- | Reduction axioms for public announcements.
-- TODO: move this to a better place, maybe SMCDEL.Language already?
reduce :: Form -> Form -> Form
reduce _  Top = Top
reduce af Bot = Neg af
reduce af (PrpF (P i)) = af `Impl` PrpF (P i)
reduce af (Neg f) = af `Impl` Neg (reduce af f)
reduce af (Conj fs) = Conj (map (reduce af) fs)
reduce af (Disj fs) = Disj (map (reduce af) fs)
reduce af (Impl f g) = reduce af f `Impl` reduce af g
reduce af (Xor fs) = af `Impl` Xor (map (reduce af) fs)
reduce af (Equi f g) = af `Impl` Equi (reduce af f) (reduce af g)
reduce af (PubAnnounce f g) = reduce af (reduce f g)
reduce _  (Forall _ _) = error "cannot reduce through quantifier"
reduce _  (Exists _ _) = error "cannot reduce through quantifier"
reduce af (K i f) = af `Impl` K i (reduce af f)
reduce af (Kw i f) = af `Impl` Disj [ K i (reduce af f) , K i (Neg $ reduce af f) ]
reduce _  (Ck _ _) = error "cannot reduce through common knowledge"
reduce _  (Ckw _ _) = error "cannot reduce through common knowledge"
reduce _  (Dk _ _) = error "cannot reduce through common knowledge"
reduce _  (Dkw _ _) = error "cannot reduce through distributed knowledge"
reduce _  (G _) = error "cannot reduce through global modality"
reduce _  (Dia _ _) = error "cannot reduce through diamond"

-- | Rewrite a formula by eliminating K operators using `push`
-- and public announcements using reduction axioms.
-- PROBLEM: this ignores the announcements already done in the list in `m`.
rewrite :: SuccinctModel -> Form -> Form
rewrite _  Top       = Top
rewrite _  Bot       = Bot
rewrite _ (PrpF (P i)) = PrpF (P i)
rewrite m (Neg f)    = Neg $ rewrite m f
rewrite m (Conj fs)   = Conj $ map (rewrite m) fs
rewrite m (Disj fs)   = Disj $ map (rewrite m) fs
rewrite m (Impl f g)  = Impl (rewrite m f) (rewrite m g)
rewrite m (Equi f g)  = Equi (rewrite m f) (rewrite m g)
rewrite m@(SMo _ _ _ mp) (K i f) = push (mp ! i) (rewrite m f)
rewrite m (Kw i f)    = rewrite m (Disj [ K i (rewrite m f), K i (Neg (rewrite m f)) ])
rewrite m (PubAnnounce f g)  = rewrite m (reduce f g)
rewrite _ f = error $ "operator not implemented: " ++ show f

canRewrite :: Form -> Bool
canRewrite Top       = True
canRewrite Bot       = True
canRewrite (PrpF (P _)) = True
canRewrite (Neg f)    = canRewrite f
canRewrite (Conj fs)   = all canRewrite fs
canRewrite (Disj fs)   = all canRewrite fs
canRewrite (Impl f g)  = canRewrite f && canRewrite g
canRewrite (Equi f g)  = canRewrite f && canRewrite g
canRewrite (K _ f) = canRewrite f
canRewrite (PubAnnounce f g)  = canRewrite f && canRewrite g
canRewrite _ = False

-- | Semantics on succinct models, via rewriting and push - TODO: test this
evalViaRewrite :: PointedSuccinctModel -> Form -> Bool
evalViaRewrite (m, s) f = boolIsTrue s (rewrite m f)

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

-- * Subformulas and Shrinking

-- | List of subprograms, including the given program itself.
-- Used by the `shrink` function for QuickCheck.
subprogs :: MenProg -> [MenProg]
subprogs (Ass p f)  = [Ass p f]
subprogs (Tst f)    = [Tst f' | f' <- shrinkform f]
subprogs (Seq mps)  = Seq mps : nub (concatMap subprogs mps)
subprogs (Cup mps)  = Cup mps : nub (concatMap subprogs mps)
subprogs (Cap mps)  = Cap mps : nub (concatMap subprogs mps)
subprogs (Inv mp)  =  mp : map Inv (subprogs mp)

shrinkprog :: MenProg -> [MenProg]
shrinkprog f = (subprogs f \\ [f]) ++ otherShrinks f
  where
    otherShrinks (Seq mps) = [Seq mps' | mps' <- powerset mps \\ [mps]]
    otherShrinks (Cup mps) = [Cup mps' | mps' <- powerset mps \\ [mps]]
    otherShrinks (Cap mps) = [Cap mps' | mps' <- powerset mps \\ [mps]]
    otherShrinks _ = []


-- * Random Generation

instance Arbitrary MenProg where
  arbitrary = sized $ randomMenProgWith defaultVocabulary
  shrink = shrinkprog

randomMenProgWith :: [Prp] -> Int -> Gen MenProg
randomMenProgWith voc 0 = oneof [ Ass <$> elements voc <*> elements [Top,Bot]
                                , pure $ Tst Top
                                , pure $ Tst Bot
                                ]
randomMenProgWith voc n = oneof [ Ass <$> elements voc <*> elements [Top,Bot]
                                , (\ p (BF f) -> Ass p f) <$> elements voc <*> randomboolformWith voc n
                                , pure $ Tst Top
                                , pure $ Tst Bot
                                , (\ (BF f) -> Tst f) <$> randomboolformWith voc n
                                , (\x y -> Seq [x,y]) <$> rmp <*> rmp
                                , (\x y z -> Seq [x,y,z]) <$> rmp <*> rmp <*> rmp
                                , (\x y -> Cup [x,y]) <$> rmp <*> rmp
                                , (\x y z -> Cup [x,y,z]) <$> rmp <*> rmp <*> rmp
                                -- , (\x y -> Cap [x,y]) <$> rmp <*> rmp
                                -- , (\x y z -> Cap [x,y,z]) <$> rmp <*> rmp <*> rmp
                                , Inv <$> rmp
                                ]
  where
    rmp = randomMenProgWith voc (n `div` 3)
