{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Pact
import Test.Hspec
import Test.QuickCheck

instance Show Err where
  show _ = "Err"

instance Show PactState where
  show _ = "PactState"

instance Show PactLog where
  show _ = "PactLog"

main :: IO ()
main = hspec $ do
    describe "Basic tests" $ do
        it "Smoke test" $ do
            print $
              run @() $
                coq_SemExp [] (TyPrim PrimUnit)
                  (Lit PrimUnit LitUnit) (unsafeCoerce () :: Pact.Any)

  where
    run :: PactM (SemTy a) -> Either Err (a, (PactState, PactLog))
    run action = unsafeCoerce $ action (error "reader") (error "state") (error "writer")
