# Instructions

0. Tested with GHC 9.10.1 and cabal-install 3.14.2.0
1. Run `cabal run`.
2. Change the relevant import lines in `Main.hs` to switch the different instances
   of `MonadPlus`. `Pred.hs` is as defined in the paper, `PredList.hs` uses native
   Haskell list type, and `PredMaybe.hs` uses the `Maybe` type.

