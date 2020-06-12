{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TemplateHaskell #-}
module EgraphTypes where


import GHC.Generics (Generic)
import Data.Hashable (hashWithSalt, hash, Hashable)
import qualified UnionFind
import Data.Primitive
import qualified Data.Vector.Fusion.Bundle as B
import qualified Data.Vector.Fusion.Bundle.Monadic as BM
import System.Mem.Weak (Weak)
import Control.Lens

import Orphans
import qualified Hashtable as HT
import BoxedVec
import Data.IntMap (IntMap)
import Data.HashMap.Strict (HashMap)
import Control.Monad.Primitive (RealWorld)
import Data.Function (on)
import Data.Foldable (Foldable(toList))


data TmHead = Add | Mul | Var Int
  deriving (Eq, Generic, Hashable)

-- for lift we need to
-- remember how to prove that a class contains a term matching a pattern
-- ,with specific equiv classes for the variables
-- ,by holding onto that Term
--
-- traditional smt solution is to hold onto whole Terms here, but we need to be able to gc redundant terms,
-- so we rebuild them again as a different type
--
-- optimizations:
-- - look for different matches if we've deleted terms/are pointing to non-canonical terms
--   - could use pattern state: for lhs add needed pattern w/ 'exists corresponding rhs match' (& sym) side condition & refuse to delete terms if would cause needed pattern to stop having matches
data Expl p =
  Congr |
  Lift !(Node p) !(Node p) p

type FindNode p = UnionFind.Node (Expl p) (ClassRoot p) RealWorld


data Node p = Node {
  -- note: FindNodes are shared between nodes with same head & equiv children
  nodeUF :: {-# UNPACK #-} !(FindNode p),
  -- is this node stored in it's root's members?
  --
  -- if `x = y` and both `f x` and `f y` exist, at most one will be canonical
  -- TODO: do we need to store this?
  nodeCanonical :: {-# UNPACK #-} !(MutVar RealWorld Bool),
  nodeTm :: !(Term p)
}

-- | reference equality
instance Eq (Node p) where
  x == y = nodeCanonical x == nodeCanonical y

data Term p = MkTerm {
   -- structural hash
  tmHash :: {-# UNPACK #-} !Int,
  tmHead :: !TmHead,
  tmBody :: {-# UNPACK #-} !(Array (Node p))
}

pattern Term :: TmHead -> [Node p] -> Term p
pattern Term hd bd <- MkTerm _ hd (toList -> bd) where
  Term hd bd = MkTerm (foldr (\x y -> y `hashWithSalt` hashTermEqual (nodeTm x)) (hash hd) bd) hd $ fromList bd



instance Eq (Term p) where
  x == y = ((==) `on` tmHash) x y
        && ((==) `on` tmHead) x y
        && (B.eq `on` (fmap nodeTm . arrayBundle . tmBody)) x y

data Pattern = Pat TmHead [Pattern] | PatVar
  deriving (Eq, Hashable, Generic)

-- match a pattern one level
matchPat :: Pattern -> Term p -> Maybe [(Pattern, Node p)]
matchPat (Pat hd bd) tm | tmHead tm /= hd = Nothing
                        | otherwise = Just $ zip bd $ toList $ tmBody tm

-- up to equiv of child terms
hashTermEquiv :: Term p -> IO Int
hashTermEquiv tm = BM.foldr (\r x -> clsHash r `hashWithSalt` x) (hash $ tmHead tm) $ BM.mapM (UnionFind.find . nodeUF) (arrayBundle $ tmBody tm)

-- structural
hashTermEqual :: Term p -> Int
hashTermEqual tm = tmHash tm

equivTerm :: Term p -> Term p -> IO Bool
equivTerm x y | tmHead x /= tmHead y = pure False
              | otherwise = BM.and $ BM.zipWithM (UnionFind.equiv `on` nodeUF) (arrayBundle $ tmBody x) (arrayBundle $ tmBody y)

data ClassRoot p = ClassRoot {
  -- nominal
  clsHash :: {-# UNPACK #-} !Int,
  -- nth vec = canonical nodes where we're the nth child
  clsParentsN :: !(Vector RealWorld (Vector RealWorld (Weak (Node p)))),
  -- | Hashmap of terms in us that we want to keep around
  --
  -- if `a == b` and the terms `f a` and `f b` exist, we only store one here
  --
  -- as an IntMap because hashing Terms needs IO
  --
  -- TODO: this should be a container with a lazy merge
  -- otherwise might as well use a hash table
  clsMembers :: {-# UNPACK #-} !(MutVar RealWorld (IntMap [Node p])),
  -- | A function of members, updated incrementally
  clsPatterns :: {-# UNPACK #-} !(MutVar RealWorld (HashMap Pattern (PatternState p)))
}

-- | Pattern + Equiv class = Query
--
-- Materialized query state
--
-- Used to store parent queries to re-run once a child query matches
--
-- TODO: add QueryTopLevel? since queries ~= callbacks
data Query p = Query {
  -- pattern we're trying to match
  queryPat :: !Pattern,
  -- term to match against pattern
  queryTm :: !(Node p)
}

-- to support deleting terms would need a (per-class) map (term => patterns matching that term)
data PatternState p = PatternMatches {
  -- matched parents that are matched due to us, needed for deletions
  _psMatchedQueries :: [(Pattern, Node p)],
  _psMatches :: [Weak (Node p)]
} | PatternNoMatches {
  _psBlockedQueries :: [Query p]
}


-- data Aggregate where
--   Agg :: (Monoid a, Typeable a) => Proxy a -> Aggregate


makeLenses ''PatternState

data EqSatState p = EqSatState {
  -- could avoid weak refs if we used finalizers on roots or such
  -- (finalizer has an entry into parents & delete a class when no parents)
  -- but would need have parent vecs be hashtables
  -- or store backref tm -> ix into child's parent vec
  --
  -- alternatively, a WeakMutableArray primitive should be doable
  --
  -- canonical nodes, keyed by hashTermEquiv and equivTerm
  nodesEquiv :: HT.WeakHashtable (EquivNode p),
  -- non-canonical Nodes, keyed by hashTermEqual & (==)
  nodesEqual :: HT.WeakHashtable (EqualNode p)
}

type EqSat p = (?eqsat :: EqSatState p)

newtype EquivNode p = EquivNode (Node p)
newtype EqualNode p = EqualNode (Node p)

instance HT.HashableIO (EquivNode p) where
  hashIO (EquivNode x) = hashTermEquiv $ nodeTm x
instance HT.MatchIO (Term p) (EquivNode p) where
  hashQ _ x = hashTermEquiv x
  matchQ tm (EquivNode nd) = equivTerm tm (nodeTm nd)
instance HT.HashableIO (EqualNode p) where
  hashIO (EqualNode x) = pure $ hashTermEqual $ nodeTm x
instance HT.MatchIO (Term p) (EqualNode p) where
  hashQ _ x = hashTermEquiv x
  matchQ tm (EqualNode nd) = pure $ tm == nodeTm nd
