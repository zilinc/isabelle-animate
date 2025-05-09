module PredMaybe where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..))


type Seq a = Maybe a

newtype Pred a = Seq (Seq a)
               deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

instance Show a => Show (Pred a) where
  show (Seq x) = show x

eval :: Eq a => Pred a -> (a -> Bool)
eval (Seq f) = (`elem` f)

