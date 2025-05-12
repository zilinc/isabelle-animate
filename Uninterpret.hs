{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}

module Uninterpret where

import Data.SBV

data A
mkUninterpretedSort ''A

data MyTypeT = MyCr1T | MyCr2T | MyCr3T | MyCr4T
mkSymbolicEnumeration ''MyTypeT