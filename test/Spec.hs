import Test.Hspec
import ExpModelChecker
import NMuddyChildren
import SucNMuddyChildren
import SucModelChecker
import SMCDEL.Language

main :: IO ()
main = hspec $ do
  describe "sucFindMuddyNumber n (sucMuddyModelFor n n) == n -1" $ do
    it "n = 4" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 4 == 4
    it "n = 5" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 5 == 5
    it "n = 6" $
      (\n -> sucFindMuddyNumber n (sucMuddyModelFor n n)) 6 == 6

  describe "isTrue" $ do
    it "random testformula  and model 1" $
      (mod1, 0::World) |= form1 `shouldBe` True

    it "random testformula  and model 2" $
      (mod2, 0::World) |= form2 `shouldBe` True

    it "random testformula  and model 3" $
      (mod3, 0::World) |= form3 `shouldBe` True

  describe "muddyModelFor 3" $ do
    context "when one child (namely 2??) is muddy" $ do -- FIXME
      it "child 0 knows" $
        muddyModelFor 3 1 |= Conj [ PrpF (P 2), K "child0" (PrpF (P 2)) ]
        `shouldBe` True
      it "child 0 does not know" $
        muddyModelFor 3 1 |= Conj [ PrpF (P 2), Neg (K "child2" (PrpF (P 2))) ]
        `shouldBe` True
      it "child 2 should know after 1 announcement" $
        muddyModelFor 3 1 |= ann (atLeastOneMuddy 3) (K "child2" (PrpF (P 2)))
        `shouldBe` True
    context "when all children are muddy" $ do
      it "no child knows their own muddiness" $
        muddyModelFor 3 3 |= Conj [ PrpF (P 0), PrpF (P 1), PrpF (P 2), nobodyKnows 3 ]
        `shouldBe` True
      it "child 0 should know child 1 and 2 are muddy" $
        muddyModelFor 3 3 |= Conj [ PrpF (P 0), PrpF (P 1), PrpF (P 2)
                                  , K "child0" (Conj [PrpF (P 1), PrpF (P 2)])]
        `shouldBe` True
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

-- some random test formulas
form1, form2, form3 :: Form
form1 = Conj [PrpF pA, Neg (K me (PrpF pA))]
form2 = Neg (K me (K jack $ Disj [PrpF pA, PrpF pB]))
form3 = Conj [ K jack (Disj [PrpF pA, PrpF pB])
             , Neg $ K me (K jack (Disj [PrpF pA, PrpF pB])) ]

-- some random test models
mod1, mod2, mod3 :: Model
mod1 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]])]
mod2 = Mo [(0, [pA]), (1, [pA, pB]), (2, [])]
          [(me, [[0, 1, 2]]), (jack, [[0], [1], [2]])]
mod3 = Mo [(0, [pA]), (1, [])] [(me, [[0, 1]]), (jack, [[0], [1]])]

-- some random propositions
pA, pB :: Prp
pA = P 0
pB = P 1

-- some random agents
me, jack :: Agent
me = "Maickel"
jack = "Jack"
