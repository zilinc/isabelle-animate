module Main where

import Control.Applicative (Alternative(..))
import PredList  -- CHANGE THIS IMPORT FOR DIFFERENT DATATYPES
-- import Pred
-- import PredMaybe


main :: IO ()
main = do
  let Seq a1 = ex1
      Seq a2 = ex2
      Seq a3 = ex3
      Seq a3' = ex3'
  putStrLn $ show a1
  putStrLn $ show a2
  putStrLn $ show a3
  putStrLn $ show a3'

ex1 = append_1_2 [1::Int,2,3] [4,5]
ex2 = append_3 [1::Int,2,3,4,5]
ex3 = append_1_3 [1::Int,2] [1,2,3,4,5]
ex3' = append_1_3 [1::Int,3] [1,2,3,4,5] 

{- [Isabelle]

inductive append :: "'a list ⇒ 'a list ⇒ 'a list ⇒ bool" where
  "append [] ys ys" |
  "append xs ys zs ⟹ append (x#xs) ys (x#zs)"

-}

append_1_2 :: [a] -> [a] -> Pred [a]
append_1_2 xs ys =
  (pure (xs, ys) >>= \case
    ([], zs) -> pure zs
    (_:_, _) -> empty) <|>
  (pure (xs, ys) >>= \case
    ([], _) -> empty
    (z:zs, ws) -> append_1_2 zs ws >>= \vs -> pure (z:vs))

append_3 :: [a] -> Pred ([a], [a])
append_3 xs =
  (pure xs >>= \ys -> pure ([], ys)) <|>
  (pure xs >>= \case
    [] -> empty
    z:zs -> append_3 zs >>= \case
      (ws, vs) -> pure (z:ws, vs))

append_1_3 :: (Eq a) => [a] -> [a] -> Pred [a]
append_1_3 xs zs =
  (pure (xs, zs) >>= \case
    ([], ys) -> pure ys
    (_, _) -> empty) <|>
  (pure (xs, zs) >>= \case
    ([], _) -> empty
    (w:ws, v:vs) | w == v -> append_1_3 ws vs
    _ -> empty)
