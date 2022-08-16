{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Pact
import Test.Hspec

main :: IO ()
main = hspec $ do
  describe "Basic tests" $ do
    it "Unit smoke test" $ do
      eval (Lit LitUnit)
        `shouldBe`
          Right ((), MkLog ())

    it "AddInt smoke test" $ do
      eval (APP (APP (Bltn AddInt)
                     (Lit (LitInteger 123)))
                (Lit (LitInteger 456)))
        `shouldBe`
          Right (579, MkLog ())

    it "SubInt smoke test" $ do
      eval (APP (APP (Bltn SubInt)
                     (Lit (LitInteger 456)))
                (Lit (LitInteger 123)))
        `shouldBe`
          Right (333, MkLog ())

    it "Unmanaged capability smoke test" $ do
      let cap = Capability (Symbol "ALLOW_USER")
                           (Lit (LitString "john"))
                           (Lit LitUnit)
      evalInModule "module"
        (WithCapability
          (Symbol "module")
          (LAM (\_ -> Lit LitUnit))
          (LAM (\_ -> Lit LitUnit))
          cap
          (RequireCapability cap))
        `shouldBe`
          Right ((), MkLog ())

    it "Managed capability smoke test" $ do
      let cap n =
            Capability (Symbol "TRANSFER")
                       (Pair (Lit (LitString "john"))
                             (Lit (LitString "jose")))
                       (Lit (LitInteger n))
      evalInModule "module"
        (Seq
          (InstallCapability (cap 100))
          (WithCapability
            (Symbol "module")
            (LAM (\_ -> Lit LitUnit))
            (LAM (\x -> APP (APP (Bltn SubInt)
                           (Fst @_ @('TyPrim 'PrimInteger) (VAR x)))
                      (Snd @('TyPrim 'PrimInteger) @_ (VAR x))))
            (cap 50)
            (RequireCapability (cap 50))))
        `shouldBe`
          Right ((), MkLog ())
