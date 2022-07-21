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

    it "AddInt smoke test" $ do
      eval (APP (APP (Bltn AddInt)
                     (Lit (LitInteger 123)))
                (Lit (LitInteger 456)))
        `shouldBe`
          Right (VInteger 579, MkLog)

    it "SubInt smoke test" $ do
      eval (APP (APP (Bltn SubInt)
                     (Lit (LitInteger 456)))
                (Lit (LitInteger 123)))
        `shouldBe`
          Right (VInteger 333, MkLog)

    it "Unmanaged capability smoke test" $ do
      let cap = Capability (Symbol "ALLOW_USER")
                           (Lit (LitString "john"))
                           (Lit LitUnit)
      evalInModule "module"
        (WithCapability
          (Symbol "module")
          (LAM (Lit LitUnit))
          (LAM (Lit LitUnit))
          cap
          (RequireCapability cap))
        `shouldBe`
          Right (VUnit, MkLog)

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
            (LAM (Lit LitUnit))
            (LAM (APP (APP (Bltn SubInt)
                           (Fst (VAR ZV)))
                      (Snd (VAR ZV))))
            (cap 50)
            (RequireCapability (cap 50))))
        `shouldBe`
          Right (VUnit, MkLog)
