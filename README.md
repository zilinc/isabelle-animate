# Instructions

0. Tested with GHC 9.10.1 and cabal-install 3.14.2.0
1. Run `cabal run`.
2. Install a compatible version of `z3` and make sure it is in your `$PATH`.
   The version requirement are listed here:
   https://github.com/LeventErkok/sbv/blob/master/SMTSolverVersions.md
   Tested with z3-4.15.0 on ubuntu.
3. Change the relevant import lines in `Main.hs` to switch the different instances
   of `MonadPlus`. `Pred.hs` is as defined in the paper, `PredList.hs` uses native
   Haskell list type, and `PredMaybe.hs` uses the `Maybe` type.
