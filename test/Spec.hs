module Main where

import Test.Hspec
import Test.QuickCheck
import SMCDEL.Language

import ExpModelChecker
import SucModelChecker
import SucNMuddyChildren
import NMuddyChildren

main :: IO ()
main = hspec $ do
  describe "sucFindMuddyNumber n (sucMuddyModelFor n n) == n-1 with" $ do
    it "n = 4" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 4 === 4
    it "n = 5" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 5 === 5
    it "n = 6" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 6 === 6

  describe "isTrue" $ do
    it "mod1 satisfies form1" $
      (mod1, 0::World) |= form1
    it "mod2 satisfies form2" $
      (mod2, 0::World) |= form2
    it "mod3 satisfies form3" $
      (mod3, 0::World) |= form3

  describe "sucMuddyModelFor 3" $ do
    context "when one child (namely 0) is muddy" $ do
      it "child 1 knows that 0 is muddy" $
        sucMuddyModelFor 3 1 |= Conj [ PrpF (P 0), K "child1" (PrpF (P 0)) ]
      it "child 0 does not know that 0 is muddy" $
        sucMuddyModelFor 3 1 |= Neg (K "child0" (PrpF (P 0)))
      it "child 0 does know this after 1 announcement" $
        sucMuddyModelFor 3 1 |= ann (atLeastOneMuddy 3) (K "child0" (PrpF (P 0)))
    context "when all children are muddy" $ do
      it "no child knows their own muddiness" $
        sucMuddyModelFor 3 3 |= Conj [ PrpF (P 0), PrpF (P 1), PrpF (P 2), nobodyKnows 3 ]
      it "child 0 knows that 1 and 2 are muddy" $
        sucMuddyModelFor 3 3 |= K "child0" (Conj [PrpF (P 1), PrpF (P 2)])
      it "no children know their own muddiness after 2 announcements" $
        sucMuddyModelFor 3 3 |= ann (atLeastOneMuddy 3)
                                (ann (nobodyKnows 3)
                                    (Conj [ Neg $ Kw "child0" (PrpF (P 0))
                                          , Neg $ Kw "child1" (PrpF (P 1))
                                          , Neg $ Kw "child2" (PrpF (P 2)) ]))
      it "all children know their own muddiness after 3 announcements" $
        sucMuddyModelFor 3 3 |= ann (atLeastOneMuddy 3)
                                (ann (nobodyKnows 3)
                                 (ann (nobodyKnows 3)
                                    (Conj [ K "child0" (PrpF (P 0))
                                          , K "child1" (PrpF (P 1))
                                          , K "child2" (PrpF (P 2)) ])))

  describe "muddyModelFor 3" $ do
    context "when one child (namely 0) is muddy" $ do
      it "child 1 knows" $
        muddyModelFor 3 1 |= Conj [ PrpF (P 0), K "child1" (PrpF (P 0)) ]
      it "child 0 does not know" $
        muddyModelFor 3 1 |= Conj [ PrpF (P 0), Neg (K "child0" (PrpF (P 0))) ]
      it "child 0 should know after 1 announcement" $
        muddyModelFor 3 1 |= ann (atLeastOneMuddy 3) (K "child0" (PrpF (P 0)))
    context "when all children are muddy" $ do
      it "no child knows their own muddiness" $
        muddyModelFor 3 3 |= Conj [ PrpF (P 0), PrpF (P 1), PrpF (P 2), nobodyKnows 3 ]
      it "child 0 should know child 1 and 2 are muddy" $
        muddyModelFor 3 3 |= Conj [ PrpF (P 0), PrpF (P 1), PrpF (P 2)
                                  , K "child0" (Conj [PrpF (P 1), PrpF (P 2)])]
      it "all children should know their own muddiness after 3 announcements" $
        muddyModelFor 3 3 |= ann (atLeastOneMuddy 3) (ann (nobodyKnows 3) (ann (nobodyKnows 3)
                                    (Conj [ PrpF (P 0), PrpF (P 1), PrpF (P 2)
                                          , K "child0" (PrpF (P 0))
                                          , K "child1" (PrpF (P 1))
                                          , K "child2" (PrpF (P 2)) ])))
    -- tests areConnected with boolIsTrue
    describe "areConnected" $
      context "connected" $ do
        it "example1" $
          areConnected (map P [1,3,9]) (Ass (P 9) Top) (map P [1,3]) (map P [1,3,9])
          `shouldBe` True
        it "example2" $
          areConnected (map P [1,3,9]) (Seq [Ass (P 9) Top, Ass (P 1) Bot]) (map P [1,3]) (map P [3,9])
          `shouldBe` True
        it "example3" $
          areConnected (map P [1,3,9]) (Cup [Ass (P 9) Top, Ass (P 1) Bot]) (map P [1,3]) (map P [1,3,9])
          `shouldBe` True
        it "example4" $
          areConnected (map P [1,3,9]) (Cup [Ass (P 9) Top, Ass (P 1) Bot]) (map P [1,3]) [P 3]
          `shouldBe` True

-- some test formulas
form1, form2, form3 :: Form
form1 = Conj [PrpF pA, Neg (K me (PrpF pA))]
form2 = Neg (K me (K jack $ Disj [PrpF pA, PrpF pB]))
form3 = Conj [ K jack (Disj [PrpF pA, PrpF pB])
             , Neg $ K me (K jack (Disj [PrpF pA, PrpF pB])) ]

-- some test models
mod1, mod2, mod3 :: Model
mod1 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]])]
mod2 = Mo [(0, [pA]), (1, [pA, pB]), (2, [])]
          [(me, [[0, 1, 2]]), (jack, [[0], [1], [2]])]
mod3 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]]), (jack, [[0], [1]])]

-- some propositions
pA, pB :: Prp
pA = P 0
pB = P 1

-- some agents
me, jack :: Agent
me = "Maickel"
jack = "Jack"
