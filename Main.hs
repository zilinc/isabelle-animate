{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main where

import Control.Applicative (Alternative(..))
import Data.Coerce
import Data.Maybe (fromJust)
import Data.SBV as SBV
import qualified Data.SBV.List as SBV
import System.IO.Unsafe (unsafePerformIO)
import Uninterpret
import Utils

-- *****************************************************************************
-- CHANGE THIS IMPORT TO TOGGLE DIFFERENT DATATYPE IMPLEMENTATION
-- import Pred
import PredList
-- import PredMaybe
-- *****************************************************************************


main :: IO ()
main = do
  dispExs "append"
    [ Ex $ append_1_2 [1::Int,2,3] [4,5]
    , Ex $ append_3 [1::Int,2,3,4,5]
    , Ex $ append_1_3 [1::Int,2] [1,2,3,4,5]
    , Ex $ append_1_3 [1::Int,3] [1,2,3,4,5]
    ]

  dispExs "append (++)"
    [ Ex $ append_1_3' [1::Integer,2] [1,2,3,4,5]
    , Ex $ append_1_3' [1::Integer,3] [1,2,3,4,5]
    ]

  dispExs "myType (!nat !myType ?string)"
    [ Ex $ baz_1_2 3 (MyCr1 "rocq" 3)
    , Ex $ baz_1_2 3 (MyCr1 "rocq" 5)
    , Ex $ baz_1_2 3 (MyCr2 3)
    ]

  dispExs "myType (!nat !string ?myType)"
    [ Ex $ baz_1_3 3 "rocq" ]

  dispExs "myType (false prem)"
    [ Ex $ foo_1_4 "rocq" 3 ]

  dispExs "clz (0^k 1 d*)"
    [ Ex $ clz_2 [False, False, False, False]
    , Ex $ clz_2 []
    , Ex $ clz_2 [True, False, False, True, True]
    , Ex $ clz_2 [False, False, True, True]
    , Ex $ clz_2 [False, False, False, True]
    , Ex $ clz_2 [False, False, False, True, False, False]
    ]

  dispExs "sat_u forward function direction"
    [ Ex $ sat_u_1_2 8 (-20)
    , Ex $ sat_u_1_2 8 0
    , Ex $ sat_u_1_2 8 200
    , Ex $ sat_u_1_2 8 4000
    ]
  
  dispExs "sat_u function inverse direction"
    [ Ex $ sat_u_1_3 8 0
    , Ex $ sat_u_1_3 8 100
    , Ex $ sat_u_1_3 8 255
    , Ex $ sat_u_1_3 8 1000
    ]

-- /////////////////////////////////////////////////////////////////////////////
-- Utils

data Ex = forall t. (Show t) => Ex (Pred t)

dispEx :: (Show t) => Pred t -> IO ()
dispEx (Seq x) = putStrLn $ "  ▹ " ++ show x

dispExs :: String -> [Ex] -> IO ()
dispExs gp exs = putStrLn (gp ++ ":") >> go exs
  where
    go [] = divLine
    go (Ex ex:exs) = dispEx ex >> go exs

divLine :: IO ()
divLine = putStrLn $ replicate 80 '-'


type Nat = Integer

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
-- When the pattern is not on a constructor

{- [Isabelle]

inductive append' :: "'a list ⇒ 'a list ⇒ 'a list ⇒ bool" where
  "append' xs ys (xs @ ys)"

rewrite it to:

inductive append' :: "'a list ⇒ 'a list ⇒ 'a list ⇒ bool" where
  "zs = xs @ ys ⟹ append' xs ys zs"

so that the patterns in the conclusion is linear.

-}

append_1_2' :: [a] -> [a] -> Pred [a]
append_1_2' xs ys =
  pure (xs, ys) >>= \case
    (xs', ys') -> pure $ xs' ++ ys'

append_1_3' :: (SymVal a, Eq a) => [a] -> [a] -> Pred [a]
{-
append_1_3' xs zs =
  pure (xs, zs) >>= \case
    (xs', zs1 ++ zs2) | zs1 == xs' -> pure zs2
    _ -> empty
-}
append_1_3' xs zs =
  pure (xs, zs) >>= \case
    (xs', zs') -> anim_p1_1 xs' zs'

  where
    {- zs = xs @ ys -}
    anim_p1_1 :: forall a. (SymVal a, Eq a) => [a] -> [a] -> Pred [a]
    anim_p1_1 xs zs = unsafePerformIO (go xs zs)
      where
        go :: forall a. (SymVal a, Eq a) => [a] -> [a] -> IO (Pred [a])
        go xs zs = do
          let c = do ys <- sList "ys"
                     return $ (literal xs) SBV.++ ys .== (literal zs)
          model <- sat c
          let mys :: Maybe [a] = getModelValue "ys" model
          return $ case mys of
                     Just ys -> pure ys
                     Nothing -> empty


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



baz_1_2 :: Nat -> MyType -> Pred String
baz_1_2 a x =
  pure (a, x) >>= \case
    (a', x') -> anim_p1_1 a' x' >>= \b -> pure b

  where
    anim_p1_1 :: Nat -> MyType -> Pred String
    anim_p1_1 a x =
      pure (a, x) >>= \case
        (a', MyCr1 c y) | a' == y -> pure c
        _ -> empty


baz_1_3 :: Nat -> String -> Pred MyType
baz_1_3 a b =
  pure (a, b) >>= \case
    (a', b') -> anim_p1_1 a' b'

  where
    anim_p1_1 :: Nat -> String -> Pred MyType
    anim_p1_1 a b =
      pure (a, b) >>= \case
        (a', b') -> pure (MyCr1 b' a')

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

foo_1_4 :: String -> Nat -> Pred (Nat, String)
foo_1_4 s b =
  pure (s, b) >>= \case
    (s', b') -> anim_p1_1 s' b'

  where
    -- How to animate the false premise?
    anim_p1_1 :: String -> Nat -> Pred (Nat, String)
    anim_p1_1 s b = unsafePerformIO $ go s b
      where
        go :: String -> Nat -> IO (Pred (Nat, String))
        go s b = do
          let c = do let mycr1 = uninterpret "mycr1" :: SString -> SWord64 -> SBV MyTypeT
                         mycr4 = uninterpret "mycr4" :: SString -> SWord64 -> SBV MyTypeT
                     constrain $ \(Forall s) (Forall t) (Forall a) (Forall b) ->
                                       mycr1 s a ./= mycr4 t b
                     t <- sString "t"
                     a <- sWord64 "a"
                     return $ mycr1 (literal s) a .== mycr4 t (literal (fromIntegral b))
          model <- sat c
          if modelExists model
            then let t :: Maybe String = getModelValue "t" model
                     a :: Maybe Nat = fromIntegral <$> (getModelValue "a" model :: Maybe Word64)
                  in return $ pure (fromJust a, fromJust t)
            else return empty



-- /////////////////////////////////////////////////////////////////////////////
-- Count leading zeros, similar to SpecTec's clz function.
-- NOTE that in sbv it already natively support clz function.

{- [Isabelle]

inductive clz :: "nat ⇒ bool list ⇒ bool" where
  "bs = replicate k false ⟹ clz k bs" |
  "bs = replicate k false @ [true] @ bs' ⟹ clz k bs"

-}

clz_2 :: [Bool] -> Pred Nat
clz_2 bs =
  (pure bs >>= \case
    bs' -> anim_p1_1 bs') <|>
  (pure bs >>= \case
    bs' -> anim_p2_1 bs')

  where
    -- bs = replicate k false
    anim_p1_1 :: [Bool] -> Pred Nat
    anim_p1_1 bs = unsafePerformIO $ go bs
      where
        go :: [Bool] -> IO (Pred Nat)
        go bs = do
          let c = do k <- sInteger "k"
                     let bs' = literal bs
                     constrain $ k .== SBV.length bs'
                     return $ \(Forall i) -> i `inRange` (0, k - 1) .=>
                       bs' `SBV.elemAt` i .== sFalse
          model <- sat c
          if modelExists model
            then let k :: Integer = fromJust $ getModelValue "k" model
                  in return $ pure k
            else return empty

    -- bs = replicate k false @ [true] @ bs'
    anim_p2_1 :: [Bool] -> Pred Nat
    anim_p2_1 bs = unsafePerformIO $ go bs
      where
        go :: [Bool] -> IO (Pred Nat)
        go bs = do
          let c = do k <- sInteger "k"
                     let bs' = literal bs
                     constrain $ k `inRange` (0, SBV.length bs' - 1)
                     return $
                       quantifiedBool (\(Forall i) -> i `inRange` (0, k - 1) .=>
                          bs' `SBV.elemAt` i .== sFalse) .&&
                       (bs' `SBV.elemAt` k .== sTrue)
          model <- sat c
          if modelExists model
            then let k :: Integer = fromJust $ getModelValue "k" model
                  in return $ pure k
            else return empty


-- /////////////////////////////////////////////////////////////////////////////
-- `sat_u` from SpecTec, with inequality premises

{- [Isabelle]

inductive sat_u :: "nat ⇒ int ⇒ nat ⇒ bool" where
  "i < 0 ⟹ sat_u N i 0" |
  "i > 2^N - 1 ⟹ sat_u N i (2^N - 1)" |
  "i ≥ 0 ⟹ i ≤ 2^N - 1 ⟹ sat_u N i (nat i)"

-}

sat_u_1_2 :: Nat -> Integer -> Pred Nat
sat_u_1_2 _N i =
  (pure (_N, i) >>= \case
    (_N', i') | i' < 0 -> pure 0
    _ -> empty) <|>
  (pure (_N, i) >>= \case
    (_N', i') | i' > 2 ^ _N' - 1 -> pure (2 ^ _N' - 1)
    _ -> empty) <|>
  (pure (_N, i) >>= \case
    (_N', i') | i' >= 0, i <= 2 ^ _N' - 1 -> pure i'
    _ -> empty)


-- A good thing about this structure is that we can get a result from each case
-- in the top-level pattern matching.
sat_u_1_3 :: Nat -> Nat -> Pred Integer
sat_u_1_3 _N n =
  (pure (_N, n) >>= \case
    (_N', 0) -> anim_p1_1
    _ -> empty) <|>
  (pure (_N, n) >>= \(_N', n') -> anim_p2_1 _N' n') <|>
  (pure (_N, n) >>= \(_N', n') -> anim_p3_1 _N' n')

  where
    anim_p1_1 :: Pred Integer
    anim_p1_1 = unsafePerformIO go
      where
        go :: IO (Pred Integer)
        go = do let c = do i <- sInteger "i"
                           return $ i .< 0
                model <- sat c
                if modelExists model
                  then let i :: Integer = fromJust $ getModelValue "i" model
                        in return $ pure i
                  else return empty

    anim_p2_1 :: Nat -> Nat -> Pred Integer
    anim_p2_1 _N n = unsafePerformIO $ go _N n
      where
        go :: Nat -> Nat -> IO (Pred Integer)
        go _N n = do
          let c = do let _N' = literal _N
                         n' = literal n
                     i <- sInteger "i"
                     constrain $ _N' .>= 0
                     constrain $ n' .>= 0
                     return $ (i .> 2 .^ _N' - 1) .&& (n' .== 2 .^ _N' - 1)
          model <- sat c
          if modelExists model
            then let i :: Integer = fromJust $ getModelValue "i" model
                  in return $ pure i
            else return empty

    anim_p3_1 :: Nat -> Nat -> Pred Integer
    anim_p3_1 _N n = unsafePerformIO $ go _N n
      where
        go :: Nat -> Nat -> IO (Pred Integer)
        go _N n = do
          let c = do let _N' = literal _N
                         n' = literal n
                     i <- sInteger "i"
                     constrain $ _N' .>= 0
                     constrain $ n' .>= 0
                     return $ (i .>= 0) .&& (i .<= 2 .^ _N' - 1) .&& (n' .== i)
          model <- sat c
          if modelExists model
            then let i :: Integer = fromJust $ getModelValue "i" model
                  in return $ pure i
            else return empty

-- /////////////////////////////////////////////////////////////////////////////
-- ibits and ishr_u, with function calls as premises.

{- [Isabelle]

inductive zip_ind :: "'a list ⇒ 'b list ⇒ ('a × 'b) list ⇒ bool" where
  "zip_ind [] _ []" |
  "zip_ind _ [] []" |
  "zip_ind xs ys zs ⟹ zip_ind (x#xs) (y#ys) ((x,y)#zs)"

inductive fold_ind :: "('a ⇒ 'b ⇒ 'b) ⇒ 'a list ⇒ 'b ⇒ 'b ⇒ bool" where
  "fold_ind f [] acc0 acc0" |
  "fold_ind f xs (f x acc0) res ⟹ fold_ind f (x # xs) acc0 res"

inductive fold_ind' :: "('a ⇒ 'b ⇒ 'b) ⇒ 'a list ⇒ 'b ⇒ 'b ⇒ bool" where
  "fold_ind' f [] acc0 acc0" |
  "xs' = xs@[x] ⟹ res = f x res' ⟹ fold_ind' f xs acc res' ⟹ fold_ind' f xs' acc res"

inductive ibits :: "nat ⇒ int ⇒ bool list ⇒ bool" where
  "is = reverse [0 .. (int N-1)] ⟹
   ids = zip is ds ⟹
   i = fold (λ(idx, d) acc. (if d then acc + 2^idx else acc)) ids 0 ⟹
   ibits N i ds"

(* Imagine the big sum was primitive *)
inductive ibits' :: "nat ⇒ int ⇒ bool list ⇒ bool" where
  "i = 2^(N-1) * ds[N-1] + ... + 1^0 * ds[0] ⟹ ibits' N i ds"

inductive ishr_u :: "nat ⇒ int ⇒ nat ⇒ int ⇒ bool" where
  "i2 ≤ 2^N - 1 ⟹
   ibits N i1 ((replicate (N - k) d1) @ (replicate k d2)) ⟹
   k = i2 mod N ⟹
   ibits N n (replicate k False @ replicate (N - k) d1) ⟹
   ishr_u N i1 i2 n"

-}

zip_ind_1_3 :: (Eq a) => [a] -> [(a, b)] -> Pred [b]
zip_ind_1_3 xs zs =
  (pure (xs, zs) >>= \case
    ([], []) -> pure []  -- We can't return anything _. We have to restrict to [].
                         -- So it is incomplete.
    _ -> empty) <|>
  (pure (xs, zs) >>= \case
    (_, []) -> pure []
    _ -> empty) <|>
  (pure (xs, zs) >>= \case
    (x:xs', (x',y):zs') | x == x' -> zip_ind_1_3 xs' zs' >>= \ys -> pure (y:ys)
    _ -> empty)

-- fold_ind_1_3_4 is not a consistent mode
fold_ind_1_3_4 :: (Eq b) => (a -> b -> b) -> b -> b -> Pred [a]
fold_ind_1_3_4 f acc0 res =
  (pure (f, acc0, res) >>= \case
    (f', acc0', res') | acc0' == res' -> pure []
    _ -> empty) <|>
  (pure (f, acc0, res) >>= \case
    (f', acc0', res') -> __can't_implement "fold_ind_1_3_4")

fold_ind_1_4 :: (a -> b -> b) -> b -> Pred ([a], b)
fold_ind_1_4 f res =
  (pure (f, res) >>= \case
    (f', res') -> pure ([], res')) <|>
  (pure (f, res) >>= \case
    (f', res') -> __can't_implement "fold_ind_1_4")

fold_ind'_1_3_4 :: (Eq b) => (a -> b -> b) -> b -> b -> Pred [a]
fold_ind'_1_3_4 f acc0 res =
  (pure (f, acc0, res) >>= \case
    (f', acc0', res') | acc0' == res' -> pure []
    _ -> empty) <|>
  (pure (f, acc0, res) >>= \case
    (f', acc0', res') -> __can't_implement "fold_ind'_1_3_4")

ibits_1_2 :: Nat -> Integer -> Pred [Bool]
ibits_1_2 _N i =
  pure (_N, i) >>= \(_N', i') ->
  anim_p3_1 i' >>= \ids ->
  anim_p1_2 _N >>= \is ->
  anim_p2_1_2 ids is

  where
    anim_p3_1 :: Integer -> Pred [(Nat, Bool)]
    anim_p3_1 i = undefined

    anim_p2_1_2 :: [(Nat, Bool)] -> [Nat] -> Pred [Bool]
    anim_p2_1_2 ids is = zip_ind_1_3 is ids

    anim_p1_2 :: Nat -> Pred [Nat]
    anim_p1_2 _N = pure $ reverse [0 .. _N]

ibits'_1_2 :: Nat -> Integer -> Pred [Bool]
ibits'_1_2 _N i =
  pure (_N, i) >>= \(_N', i') -> anim_p1_1 _N' i'

  where
    anim_p1_1 :: Nat -> Integer -> Pred [Bool]
    anim_p1_1 _N i = unsafePerformIO $ go _N i
      where
        go :: Nat -> Integer -> IO (Pred [Bool])
        go _N i = do
          let c = do let _N' = literal _N
                         i'  = literal i
                     ds :: SList Bool <- sList "ds"
                     constrain $ _N' .>= 0
                     constrain $ SBV.length ds .== _N'
                     -- SBV doesn't support it.
                     return $ i' .== SBV.foldr (\k acc -> ite (ds SBV.!! k) (2 .^ (sFromIntegral k :: SWord8)) 0 + acc)
                                               0
                                               (literal (reverse [0 .. _N - 1]))
          model <- sat c
          if modelExists model
            then let ds :: [Bool] = fromJust $ getModelValue "ds" model
                  in return $ pure ds
            else return empty

ishr_u_1_2_3 :: Nat -> Integer -> Nat -> Pred Integer
ishr_u_1_2_3 _N i1 i2 =
  pure (_N, i1, i2) >>= \case
    (_N', i1', i2') -> anim_p1_1_2_3_4 _N' i1' i2'

  where
    anim_p1_1_2_3_4 :: Nat -> Integer -> Nat -> Pred Integer
    anim_p1_1_2_3_4 _N i1 i2 = unsafePerformIO $ go _N i1 i2
      where
        go :: Nat -> Integer -> Nat -> IO (Pred Integer)
        go _N i1 i2 = do
          let c = do k <- sInteger "k"
                     constrain $ k .>= 0
                     let _N' = literal _N
                         i1' = literal i1
                         i2' = literal i2
                     constrain $ _N' .>= 0
                     constrain $ i2' .>= 0
                     let c1 = i2' .<= 2 .^ _N' - 1
                         c2 = undefined
                         c3 = k .== i2' `sMod` _N'
                         c4 = undefined
                     return $ sAnd [c1,c2,c3,c4]
          model <- sat c
          if modelExists model
            then let n :: Integer = fromJust $ getModelValue "n" model
                  in return $ pure n
            else return empty


