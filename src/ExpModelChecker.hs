{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module ExpModelChecker where

import Data.List
import Data.Maybe
import SMCDEL.Language

-- TODO: replace with `Update` from SMCDEL
class UpdateAble a where
  (!) :: a -> Form -> a

instance UpdateAble Model where
  (!) = publicAnnounce

-- Assignments are a list of propositions that are true in a world
type Assignment = [Prp]

-- Worlds are a possible reality where propositions get assigned a truth truthvalue
type World = Int

-- An explicit model is represented by a list of worlds with their assignments,
-- and a list of agents with their relations (relations: list of lists of worlds.
-- all worlds should be present exactly once, and  being in the same list means
-- the worlds are indistinguishable)
data Model = Mo [(World,Assignment)] [(Agent,[[World]])] deriving (Eq,Ord,Show)
instance Pointed Model Int

-- diamond version of announcement: f is true and after announcing it we have g
ann :: Form -> Form -> Form
ann f g = Conj [f , PubAnnounce f g]

-- a version of an exiting function that returns the second of a tuple of which
-- the first in the input from a list of tuples.
myLookup :: Eq a => a -> [(a,b)] -> Maybe b
myLookup _ []       = Nothing
myLookup x (y:rest) = if x == fst y then Just (snd y) else myLookup x rest

-- version of lookup that assumes the first one of the tuple exists in the list
unsafeLookup :: Eq a => a -> [(a,b)] -> b
unsafeLookup x list = Data.Maybe.fromMaybe undefined (lookup x list)

-- returns all the worlds of a model
worldsOf :: Model -> [World]
worldsOf (Mo val _rel) = map fst val

instance HasVocab Model where
  vocabOf (Mo worlds _) = nub $ concatMap snd worlds

-- shorthand for funstion: isTrue
instance Semantics (Model,World) where
  isTrue = eval

-- returns whether a Form is true in a pointed model (a perticular world in a model)
eval :: (Model,Int) -> Form -> Bool
eval _  Top       = True
eval _  Bot       = False
eval (Mo val _,w) (PrpF p) = p `elem` unsafeLookup w val
eval a (Neg f)    = not $ eval a f
eval a (Conj fs)   = all (eval a) fs
eval a (Disj fs)   = any (eval a) fs
eval a (Impl f g)  = not (eval a f) || eval a g
eval a (Equi f g)  = eval a f == eval a g
eval (m, w) (K i f) =
  all
    (\w' -> eval (m,w') f)
    (localState (m, w) i)
eval a (Kw i f) = eval a (Disj [ K i f, K i (Neg f) ])
eval (m, w) (PubAnnounce f g)  = not (eval (m,w) f) ||
                           eval (m ! f, w) g
eval _ _ = error "not implemented by this system"

-- returns worlds that are reachable for an agent from the actual world?
localState :: (Model,Int) -> Agent -> [Int]
localState (Mo _ rel,w) i = case filter (w `elem`) (unsafeLookup i rel) of
  []      -> error $ "agent " ++ i ++ " has no equivalence class"
  [set]   -> set
  -- at least 2 elements:
  (_:_:_) -> error $ "agent " ++ i ++ " has more than one equivalence class: " ++ show (unsafeLookup i rel)

-- returns the new model that results from having a public announcement in a model
publicAnnounce :: Model -> Form -> Model
publicAnnounce m@(Mo val rel) f = Mo newVal newRel where
  newVal = [ (w,v) | (w,v) <- val, (m,w) |= f ]
  newRel = [ (i, filter (/= []) $ prune parts) | (i,parts) <- rel ]
  prune :: [[Int]] -> [[Int]]
  prune = map (\ws -> [w | w <- ws, w `elem` map fst newVal])
