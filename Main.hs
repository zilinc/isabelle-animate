{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Control.Applicative (Alternative(..))

-- *****************************************************************************
-- CHANGE THIS IMPORT TO TOGGLE DIFFERENT DATATYPE IMPLEMENTATION
-- import Pred
import PredList
-- import PredMaybe
-- *****************************************************************************


main :: IO ()
main = do
  dispExs
    [ Ex $ append_1_2 [1::Int,2,3] [4,5]
    , Ex $ append_3 [1::Int,2,3,4,5]
    , Ex $ append_1_3 [1::Int,2] [1,2,3,4,5]
    , Ex $ append_1_3 [1::Int,3] [1,2,3,4,5]
    ]

  dispExs
    [ Ex $ baz_1_2 3 (MyCr1 "my" 3)
    , Ex $ baz_1_2 3 (MyCr1 "my" 5)
    , Ex $ baz_1_2 3 (MyCr2 3)
    ]

  dispExs [ Ex $ baz_1_3 3 "yours" ]




-- /////////////////////////////////////////////////////////////////////////////
-- Utils

data Ex = forall t. (Show t) => Ex (Pred t)

dispEx :: (Show t) => Pred t -> IO ()
dispEx (Seq x) = putStrLn $ "▹ " ++ show x

dispExs :: [Ex] -> IO ()
dispExs [] = divLine
dispExs (Ex ex:exs) = dispEx ex >> dispExs exs

divLine :: IO ()
divLine = putStrLn $ replicate 80 '-'


-- /////////////////////////////////////////////////////////////////////////////
-- `append` example from the Isabelle animation paper

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


-- /////////////////////////////////////////////////////////////////////////////
-- `myType` example from Avishkar's Rocq experiments


{- [Rocq]

Inductive myType : Set :=
| mycr2 : nat -> myType
| mycr4 : string -> nat -> myType
| mycr1 : string -> nat -> myType
| mycr3 : myType.

Inductive baz : nat -> myType -> string -> Prop :=
| bazCon : forall (a : nat), forall (x : myType), forall (b : string),
    mycr1 b a = x -> baz a x b.

-}

type Nat = Int

data MyType where
  MyCr2 :: Nat -> MyType
  MyCr4 :: String -> Nat -> MyType
  MyCr1 :: String -> Nat -> MyType
  MyCr3 :: MyType
  deriving (Show)

-- XXX | {- [Rewrite = on `myType` type to an inductive definition]
-- XXX | 
-- XXX | Inductive myTypeEq : myType -> myType -> Prop :=
-- XXX | | mycr2_eq : forall (n m : nat), n = m -> myTypeEq (mycr2 n) (mycr2 m)
-- XXX | | mycr4_eq : forall (u v : string), forall (m n : nat),
-- XXX |     u = v -> m = n -> myTypeEq (mycr4 u m) (mycr4 v n)
-- XXX | | mycr1_eq : forall (u v : string), forall (m n : nat),
-- XXX |     u = v -> m = n -> myTypeEq (mycr1 u m) (mycr1 v n)
-- XXX | | mycr3_eq : myTypeEq mycr3 mycr3.
-- XXX | 
-- XXX | -}


mycr1_eq_2_3 :: Nat -> MyType -> Pred String
mycr1_eq_2_3 a x =
  pure (a, x) >>= \case
    (a', MyCr1 c y) | a' == y -> pure c
    _ -> empty

baz_1_2 :: Nat -> MyType -> Pred String
baz_1_2 a x =
  pure (a, x) >>= \case
    (a', x') -> mycr1_eq_2_3 a' x' >>= \b -> pure b


mycr1_eq_1_2 :: Nat -> String -> Pred MyType
mycr1_eq_1_2 a b =
  pure (a, b) >>= \case
    (a', b') -> pure (MyCr1 b' a')

baz_1_3 :: Nat -> String -> Pred MyType
baz_1_3 a b =
  pure (a, b) >>= \case
    (a', b') -> mycr1_eq_1_2 a' b'

-- What is the procedure to animate the equality?


-- /////////////////////////////////////////////////////////////////////////////
-- Similar to Avishkar's example above, but with a false premise.
{- [Rocq]

Inductive myType : Set :=
| mycr2 : nat -> myType
| mycr4 : string -> nat -> myType
| mycr1 : string -> nat -> myType
| mycr3 : myType.

Inductive foo : nat -> myType -> string -> Prop :=
| fooCon : forall (a b : nat), forall (x : myType), forall (s t : string),
    mycr1 s a = mycr4 t b -> foo s a t b.

-}

-- How to animate the false premise?