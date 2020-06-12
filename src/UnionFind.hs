{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- | Union-find-explain/proof producing union find
--
-- `O(log n)` union (assuming union by size?) and `O(k)` explain,  k = proof size & n = number of nodes
--
-- is a traditional union find + a proof forest
--
-- there also exists a version with `O(α(n))` union and `O(k log n)` explain, see "Proof-producing Congruence Closure" (https://www.cs.upc.edu/~oliveras/espai/papers/rta05.pdf)
--
-- the normal union-find-explain used in smt solvers congruence closure is eager path compression + a proof forest (and uses a list of members of each class (needed anyways) for eager path compression), this does lazy path compression to avoid needing to traverse members of congruence classes on merges
--
-- the hope is that eager path compression is worth avoiding in eqsat (did some profiling and in smt at least for yices2 it's not a big part of congr closure's cost)
--
-- the other thing that we could do is try to produce better (smaller) proofs by keeping around (some?) redundant equalities we're told about (or switching to new equalities that give smaller proofs). not doing that for now but smaller proofs = less memory usage after merging redundant terms


-- old:
-- -- plan is to build CC elem as union-find elem + fn body w/ union-find elems as subterms
-- -- so we can hold onto union-find elems instead of terms for children of redundant terms
-- -- or when ackermannization causes the sat solver to have a simpler (single variable) proof

module UnionFind (Node, new, find, find', union, equiv, explain) where

import Orphans
import Data.Struct.Internal
import Control.Lens hiding (set)
import Control.Monad.Primitive (stToPrim)
import Control.Monad.ST (ST)

data NodeTag = Child | ChildReversed | Root
  deriving (Eq)

-- | struct
--
-- @
-- data Node p r s = Node {
--   tag :: NodeTag,
--   prfOrRoot :: if tag == Root then r else p
--   prfRhs :: if tag == Root then Null else Node p r s
--   parent :: if tag == Root then Null else Node p r s
-- }
-- @
--
-- if proofs knew how to reverse could avoid tag
--
-- `prfRhs`s should form a path to the root
--
-- this is two different union-find structures with the same root
newtype Node p r s = Node (Object s)
  deriving (Struct, Eq)

nodeTag :: Field (Node p r) NodeTag
nodeTag = field 0

new :: MonadPrim s m => r -> m (Node p r s)
new !r = stToPrim $ do
  x <- alloc 4
  setField nodeTag x Root
  setField (field 1) x r
  set (slot 2) x nullNode
  set (slot 3) x nullNode
  pure x
  where
  nullNode :: Node p r s
  nullNode = Nil

find :: MonadPrim s m => Node p r s -> m r
find a = getField (field 1) =<< find' a

find' :: MonadPrim s m => Node p r s -> m (Node p r s)
find' x = stToPrim $ getField nodeTag x >>= \case
  Root -> pure x
  _ -> do
    y <- get (slot 3) x
    r <- find' y
    set (slot 3) x r
    pure r

-- | merges y into x, p should be a proof of x == y, or of y == x if !dr
union :: MonadPrim s m => Node p r s -> Node p r s -> p -> Bool -> r -> m ()
union x y pr dr !r = stToPrim $ do
  flipProofs y
  setField nodeTag y (if dr then ChildReversed else Child)
  setField (field 1) y pr
  set (slot 2) y x
  
  yr <- find' y
  xr <- find' x
  set (slot 3) yr xr
  setField (field 1) xr r

-- make x be the root of the proof tree it's in
flipProofs :: Node p r s -> ST s ()
flipProofs x = getField nodeTag x >>= \case
  Root -> pure ()
  dr -> do
    pr <- getField (field 1) x
    y <- get (slot 2) x
    flipProofs y
    setField nodeTag y (rev dr)
    setField (field 1) y pr
    set (slot 2) y x
  where
    rev Child = ChildReversed
    rev ChildReversed = Child



equiv :: MonadPrim s m => Node p r s -> Node p r s -> m Bool
equiv x y = (==) <$> find' x <*> find' y

explain :: MonadPrim s m => Node p r s -> Node p r s -> m (Maybe [(p, Bool)])
explain a b = stToPrim $ equiv a b >>= \case
  False -> pure Nothing
  True -> do
    xp <- go a []
    yp <- go b []
    -- TODO: strip common part
    pure $ Just (reverse xp ++ over (traverse . _2) not yp)
  where
    go x l = getField nodeTag x >>= \case
      Root -> pure l
      tg -> do
        s <- (,tagb tg) <$> getField (field 1) x
        y <- get (slot 2) x
        go y (s:l)

    tagb Child = True
    tagb ChildReversed = False
