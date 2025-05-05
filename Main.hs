module Main where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..))
-- import Data.Foldable (fold)
import Data.List (intercalate)
import Prelude hiding (seq)

main :: IO ()
main = do
  let Seq a = ex2
  putStrLn $ show a

ex1 = append_1_2 [1::Int,2,3] [4,5]
ex2 = append_3 [3::Int,4,5,5,5]


data Seq a = Empty | Insert a (Pred a) | Union [Pred a]

instance Show a => Show (Seq a) where
  show Empty = ""
  show (Insert x xq) = show x ++ ", " ++ show xq
  show (Union xqs) = intercalate ", " (show <$> xqs)

data Pred a = Seq (Seq a)

instance Show a => Show (Pred a) where
  show (Seq x) = show x

instance Functor Pred where
  fmap f (Seq g) = Seq $ case g of
    Empty -> Empty
    Insert x xq -> Insert (f x) (fmap f xq)
    Union xqs -> Union (fmap f <$> xqs)

instance Applicative Pred where
  pure x = Seq (Insert x empty)
  liftA2 h (Seq f) (Seq g) = Seq $ case (f, g) of
    (Empty, _) -> Empty
    (_, Empty) -> Empty
    (Insert x xq, Insert y yq) -> Insert (h x y) (liftA2 h xq yq)
    (Insert x xq, Union yqs) -> Union $ ((h x <$>) <$> yqs) ++ (liftA2 h xq <$> yqs)
    (Union xqs, Insert y yq) -> Union $ (((flip h) y <$>) <$> xqs) ++ (flip (liftA2 h) yq <$> xqs)
    (Union xqs, Union yqs) -> Union $ liftA2 h <$> xqs <*> yqs

instance Monad Pred where
  Seq g >>= f = Seq $ case g of
                  Empty -> Empty
                  Insert x xq -> Union [f x, xq >>= f]
                  Union xqs -> Union ((>>= f) <$> xqs)

instance Alternative Pred where
  empty = Seq Empty
  (Seq f) <|> (Seq g) = Seq $
    case f of
      Empty -> g
      Insert x xq -> Insert x (xq <|> Seq g)
      Union xqs -> Union $ xqs <> [Seq g]

instance MonadPlus Pred

eval :: Eq a => Pred a -> (a -> Bool)
eval (Seq f) = member f

member :: Eq a => Seq a -> a -> Bool
member Empty _ = False
member (Insert y yq) x = x == y || eval yq x
member (Union xqs) x = any (flip eval x) xqs

append :: ([a] -> [a] -> [a]) -> Pred [a]
append = undefined

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

