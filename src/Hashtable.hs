{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- module WeakHashtable (
--   WeakHashtable, lookup, forWeakHashtable_, resize, insert, size
--                  ) where

module Hashtable where

import Prelude hiding (lookup)
import Data.Primitive.Array
import Data.Primitive.MutVar
import GHC.Prim (reallyUnsafePtrEquality#, RealWorld)
import GHC.Exts (unsafeCoerce#)
--import GHC.Types (Word(W#))
--import GHC.Prim (timesWord2#)
--import GHC.Prim (timesWord#)
--import GHC.Prim (plusWord#)
import GHC.Exts (isTrue#)
import System.Mem.Weak (deRefWeak, Weak)
import GHC.Base (modInt)
import Data.Proxy (Proxy(Proxy))
import Control.Monad (when)


data Content a = Content {
  cValues :: {-# UNPACK #-} !(MutableArray RealWorld (Weak a)),
  cSize :: {-# UNPACK #-} !Int,
  cUsedSlots :: {-# UNPACK #-} !(MutVar RealWorld Int),
  cTombstoneSlots :: {-# UNPACK #-} !(MutVar RealWorld Int),
  cMaxUsed :: {-# UNPACK #-} !Int,
  cMinUsed :: {-# UNPACK #-} !Int
}


newtype WeakHashtable a = WeakHashtable { unWeakHashtable :: MutVar RealWorld (Content a) }

mixHash :: Int -> Int
mixHash h = fromIntegral $ fromIntegral h * (11400714819323198485 :: Word)
{-# INLINE mixHash #-}

-- times128 :: (Word, Word) -> (Word, Word) -> (Word, Word)
-- times128 (W# a1, W# a0) (W# b1, W# b0) = (W# p1, W# p0) where
--   !(# c1, p0 #) = timesWord2# a0 b0
--   p1a = timesWord# a1 b0
--   p1b = timesWord# a0 b1
--   p1c = plusWord# p1a p1b
--   p1 = plusWord# p1c c1
-- {-# INLINE times128 #-}

-- replacement for mod
range :: Int -> Int -> Int
range x y = x `modInt` y
-- range x y = fromIntegral $ fst $ times128 (0, fromIntegral x) (0, fromIntegral y)
{-# INLINE range #-}

data Null = Null
data Empty = Empty

isNull :: a -> Bool
isNull x = isTrue# (unsafeCoerce# reallyUnsafePtrEquality# Null x)
{-# INLINE isNull #-}

isEmpty :: a -> Bool
isEmpty x = isTrue# (unsafeCoerce# reallyUnsafePtrEquality# Empty x)

new :: IO (WeakHashtable a)
new = newSized 16

newSized :: Int -> IO (WeakHashtable a)
newSized n = WeakHashtable <$> (newMutVar =<< cNewSized n)

cNewSized :: Int -> IO (Content a)
cNewSized n = do
  let n' = max n 2
  a <- newArray n' $! unsafeCoerce# Null
  used <- newMutVar 0
  tombstones <- newMutVar 0
  pure $ Content { cValues = a, cSize = n', cUsedSlots = used, cMinUsed = 0, cMaxUsed = (n' * 3) `div` 4, cTombstoneSlots = tombstones }

class HashableIO a where
  hashIO :: a -> IO Int

class MatchIO q a where
  hashQ :: Proxy a -> q -> IO Int
  matchQ :: q -> a -> IO Bool

-- | returns first match, stops at empty slots
lookup :: forall q a. MatchIO q a => WeakHashtable a -> q -> IO (Maybe a)
lookup (WeakHashtable rf) q = do
  h <- hashQ (Proxy :: Proxy a) q
  c <- readMutVar rf
  iterH c h \_ _ x -> matchQ q x >>= \case
    True -> pure $ Just x
    False -> pure Nothing
{-# INLINABLE lookup #-}

lookupWeak :: MatchIO q a => WeakHashtable a -> q -> IO (Maybe (a, Weak a))
lookupWeak = undefined
-- lookupWeak t h f = lookup t h \s rf -> deRefWeak rf >>= \case
--   Nothing -> deleteSlot t s >> pure Nothing
--   Just x -> f x >>= \case { True -> pure (Just (x, rf)); False -> pure Nothing }
-- {-# INLINABLE lookupWeak #-}

forWeakHashtable_ :: WeakHashtable a -> (Int -> Weak a -> IO ()) -> IO ()
forWeakHashtable_ (WeakHashtable h) f = flip cForWeakHashtable_ f =<< readMutVar h
{-# INLINE forWeakHashtable_ #-}

cForWeakHashtable_ :: Content a -> (Int -> Weak a -> IO ()) -> IO ()
cForWeakHashtable_ Content{..} f = go 0 where
  go !n | n >= cSize = pure ()
        | otherwise = do
            x <- readArray cValues n
            when (not (isNull x || isEmpty x)) $ f n x
            go (n+1)
{-# INLINE cForWeakHashtable_ #-}


size :: WeakHashtable a -> IO Int
size (WeakHashtable h) = cSize <$> readMutVar h

resize :: HashableIO a => WeakHashtable a -> IO ()
resize t@(WeakHashtable h) = do
  old <- readMutVar h
  used <- readMutVar $ cUsedSlots old
  tombstones <- readMutVar $ cTombstoneSlots old
  let used_old = used - tombstones
  new <- cNewSized (used_old*2)
  writeMutVar h new
  cForWeakHashtable_ old \_ x -> insert t x
{-# INLINABLE resize #-}


-- | inserts even if already exists
insert :: HashableIO a => WeakHashtable a -> Weak a -> IO ()
insert m@(WeakHashtable rf) v = do
  Content{..} <- readMutVar rf
  used <- readMutVar cUsedSlots
  if used < cMaxUsed then
    deRefWeak v >>= \case
      Nothing -> pure ()
      Just vx -> do
        h <- hashIO vx
        let !n0 = range (mixHash h) cSize
        let go !n = do
              x <- readArray cValues n
              if isNull x || isEmpty x then do
                writeArray cValues n v
                when (isNull x) $ modifyMutVar cUsedSlots (+1)
                else go n2
              where n1 = n+1; n2 = if n1 < cSize then n1 else 0
        go n0
  else do
    resize m
    insert m v
{-# INLINABLE insert #-}

iterH :: Content a -> Int -> (Int -> Weak a -> a -> IO (Maybe b)) -> IO (Maybe b)
iterH c@Content{..} h f = do
  let !n0 = range (mixHash h) cSize
  let go !n = do
        x <- readArray cValues n
        if isNull x then pure Nothing else
          if isEmpty x then go n2 else
          deRefWeak x >>= \case
            Nothing -> do
              deleteIx c n
              go n2
            Just x' -> f n x x' >>= \case
              Just r -> pure $ Just r
              Nothing -> go n2 
        where n1 = n+1; n2 = if n1 < cSize then n1 else 0
  go n0
{-# INLINE iterH #-}

deleteIx :: Content a -> Int -> IO ()
deleteIx Content{..} ix = do
  modifyMutVar cTombstoneSlots (+1)
  writeArray cValues ix $! unsafeCoerce# Empty

-- | stops on True and empty slots
delete :: forall q a. MatchIO q a => WeakHashtable a -> q -> IO ()
delete (WeakHashtable rf) q = do
  c@Content{..} <- readMutVar rf
  h <- hashQ (Proxy :: Proxy a) q
  _ <- iterH c h \n _ y -> matchQ q y >>= \case 
        True -> deleteIx c n >> pure (Just ())
        False -> pure Nothing
  pure ()
{-# INLINABLE delete #-}

