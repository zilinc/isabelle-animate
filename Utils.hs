{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils where

import Control.Monad (unless)

__impossible :: String -> a
__impossible msg = error $ msg ++ ": the 'impossible' happened!"

__exhaustivity :: String -> a
__exhaustivity msg = error $ msg ++ ": `otherwise' is not used for clarity, so GHC doesn't know the guards are exhaustive"

__todo :: String -> a
{-# WARNING __todo "TODO" #-}
__todo msg = error $ "TODO: " ++ msg

__todo_ :: a
__todo_ = __todo "(???)"

__fixme :: a -> a
{-# WARNING __fixme "FIXME" #-}
__fixme = id

__assert :: Monad m => Bool -> String -> m ()
__assert ass msg = unless ass $ error ("ASSERTION FAILED: " ++ msg)

__assert_ :: Bool -> String -> x -> x
__assert_ ass msg x = if ass then x else error ("ASSERTION FAILED: " ++ msg)