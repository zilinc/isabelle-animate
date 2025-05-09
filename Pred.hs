module Pred where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..))
import Data.List (intercalate)


data Seq a = Empty | Insert a (Pred a) | Union [Pred a]

instance Show a => Show (Seq a) where
  show Empty = ""
  show (Insert x xq) = show x ++ ", " ++ show xq
  show (Union xqs) = intercalate ", " (show <$> xqs)

newtype Pred a = Seq (Seq a)

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

