{-# LANGUAGE TypeFamilies #-}
module Orphans where

import Prelude hiding (fail)
import Control.Monad.Primitive
import Data.Monoid
import Control.Monad.Fail

instance PrimMonad m => PrimMonad (Alt m) where
  type PrimState (Alt m) = PrimState m
  primitive a = Alt (primitive a)

instance MonadFail m => MonadFail (Alt m) where
  fail a = Alt (fail a)