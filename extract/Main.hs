module Main where

import Pact
import Test.Hspec

main :: IO ()
main = hspec $ do
    describe "Basic tests" $ do
        it "Unit smoke test" $ do
            print $ eval (TyPrim PrimUnit) (Lit p LitUnit)

        it "Lambda AddInt smoke test" $ do
            print $ eval (TyPrim PrimInteger)
              (APP t t
                   (APP t t
                        (Bltn t AddInt)
                        (Lit p (LitInteger 123)))
                   (Lit p (LitInteger 456)))

  where
    t :: Ty
    t = error "Ty argument ignored"

    p :: PrimType
    p = error "PrimType argument ignored"
