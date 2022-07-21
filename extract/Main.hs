module Main where

import Pact
import Test.Hspec

main :: IO ()
main = hspec $ do
    describe "Basic tests" $ do
        it "Unit smoke test" $ do
            eval (Lit LitUnit)
              `shouldBe`
                Right (VUnit, MkLog)

        it "Lambda AddInt smoke test" $ do
            eval
              (APP (APP (Bltn AddInt)
                        (Lit (LitInteger 123)))
                   (Lit (LitInteger 456)))
              `shouldBe`
                Right (VInteger 579,MkLog)
