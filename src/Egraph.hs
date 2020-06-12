{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RecursiveDo #-}


-- | e-peg/egraph
--
-- TODO:
-- - merging terms / adding to equiv classes
--   - congr closure
-- - equality constraints / nonlinear variables
-- - aggregates
-- - tests
--
-- - think about doing something special for e.g. AC

-- TODO: would be nice to be able to use union-find like when no function symbols
-- & only do work for function symbols
module Egraph where

import Control.Lens
--import Control.Lens.Extras (is)
import Control.Monad.Zip (MonadZip(mzipWith))
import Data.Foldable (Foldable(toList))
import Data.Function (on)
import Data.Primitive
import GHC.Weak
import System.CPUTime (getCPUTime)

-- import Orphans
import qualified Hashtable as HT
import EgraphTypes
import qualified UnionFind
import BoxedVec
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap (IntMap)
import Data.Coerce (coerce)
import Control.Monad.Trans.Maybe (MaybeT(runMaybeT))
import Data.Traversable (for)
import Control.Monad (mzero, when)
import Control.Monad.IO.Class (MonadIO(liftIO))

runQuery :: EqSat p => Query p -> IO ()
-- TODO: assert or check not already matched?
runQuery q@(Query p tm) = case matchPat p (nodeTm tm) of
  Nothing -> pure ()
  Just bnds -> do
    x <- runMaybeT $ for bnds \(pat, ctm) -> when (pat /= PatVar) $ do
      cr <- UnionFind.find $ nodeUF ctm
      ps <- liftIO $ patternState cr pat
      if has (psMatches . _head) ps then
        pure ()
      else do
        modifyMutVar (clsPatterns cr) (\m -> m & ix p . psBlockedQueries %~ (q:))
        mzero
    when (has _Just x) $ do
      r <- mkWeak tm tm Nothing
      cr <- UnionFind.find $ nodeUF tm
      m <- readMutVar (clsPatterns cr)
      if has (ix p . psBlockedQueries . _head) m then do
        writeMutVar (clsPatterns cr) (m & ix p .~ PatternMatches [] [r])
        forOf_ (ix p . psBlockedQueries . each) m runQuery
      else do
        writeMutVar (clsPatterns cr) (m & ix p . psMatches %~ (r:))
  where
  patternState :: EqSat s => ClassRoot s -> Pattern -> IO (PatternState s)
  patternState cls p = do
    m <- readMutVar $ clsPatterns cls
    case m ^? ix p of
      Just r -> pure r
      Nothing -> do
        writeMutVar (clsPatterns cls) (m & at p .~ Just (PatternNoMatches []))
        members <- readMutVar $ clsMembers cls
        forOf_ (traverse . traverse) members \x -> runQuery $ Query p x
        m' <- readMutVar (clsPatterns cls)
        pure $ m' ^?! ix p



-- find a node for term if it exists
findTerm' :: EqSat p => Term p -> IO (Maybe (Node p, Weak (Node p)))
findTerm' tm = coerce $ HT.lookupWeak (nodesEqual ?eqsat) tm

findTerm :: EqSat p => Term p -> IO (Maybe (Node p))
findTerm tm = fmap fst <$> findTerm' tm

-- find a node equiv to term if exists, assumes not a leaf
findEquiv :: EqSat p => Term p -> IO (Maybe (Node p))
findEquiv tm = fmap (coerce . fst) <$> HT.lookupWeak (nodesEquiv ?eqsat) tm

makeTerm :: EqSat p => Term p -> IO (Node p)
makeTerm tm = findTerm tm >>= \case
  Just x -> pure x
  Nothing -> do
    findEquiv tm >>= \case
      Just x | nodeTm x == tm -> pure x
             | otherwise -> do
        x' <- Node (nodeUF x) <$> newMutVar False <*> pure tm
        xrf' <- mkWeak x' x' Nothing
        HT.insert (nodesEqual ?eqsat) $ coerce xrf'
        pure x'
      Nothing -> mdo
        let bd = tmBody tm
        -- TODO: do something better here
        hash <- fromIntegral <$> getCPUTime
        h <- hashTermEquiv tm
        cls <- ClassRoot hash
          <$> newVector_
          <*> newMutVar (fromList [(h, [nd])])
          <*> newMutVar mempty
        ufnd <- UnionFind.new cls
        nd <- Node ufnd <$> newMutVar True <*> pure tm
        ndref <- mkWeak nd nd Nothing
        HT.insert (nodesEquiv ?eqsat) $ coerce ndref
        ifor_ (tail $ toList bd) \i pnd -> do
          cls' <- UnionFind.find $ nodeUF pnd
          v <- readVectorDef (clsParentsN cls') i newVector_
          addVector ndref v
        pure nd



data Proof p = LiftPrf Bool {- ^ False = reversed -} p | CongrPrf TmHead (Array [Proof p])

explain' :: Node p -> Node p -> IO (Maybe [Proof p])
explain' x y = UnionFind.equiv (nodeUF x) (nodeUF y) >>= \case
  True -> Just <$> explain x y
  False -> pure Nothing

explain :: Node p -> Node p -> IO [Proof p]
explain x y = do
  Just p1 <- UnionFind.explain (nodeUF x) (nodeUF y)
  go x p1 y where
    go a ((Congr,_):bs) c = go a bs c
    go a ((Lift lx rx p,rv):bs) c = do
      let (l,r) = if rv then (lx,rx) else (rx,lx)
      rs <- go r bs c
      cgr <- g a l
      pure (cgr ++ (LiftPrf rv p:rs))
    go a [] b = g a b

    g a b | ((/=) `on` (tmHead . nodeTm)) a b = error "explain internal error"
          | ((==) `on` nodeTm) a b = pure []
          -- TODO: avoid intermediate array
          | otherwise = ((:[]) . CongrPrf (tmHead $ nodeTm a)) <$> (sequenceA $ mzipWith explain (tmBody $ nodeTm x) (tmBody $ nodeTm y))



-- pf should be a proof of x == y
do_merge :: EqSat p => Node p -> Node p -> Expl p -> IO ()
do_merge a b pf = do
  -- TODO: algebraic datatypes & otherwise injective functions
  let an = nodeUF a
      bn = nodeUF b
  ar <- UnionFind.find an
  br <- UnionFind.find bn

  writeMutVar (clsMembers ar) =<< IntMap.unionWith (++) <$> readMutVar (clsMembers ar) <*> readMutVar (clsMembers br)
  
  -- update patterns
  -- if prf is congr can check if b's prf is congr & if so union w/ p's prfRhs instead
  UnionFind.union an bn pf True ar

  iforVector_ (clsParentsN br) \i vb -> do
    va <- readVectorDef (clsParentsN ar) i newVector_
    forVector_ vb \prf -> deRefWeak prf >>= \case
      Nothing -> pure ()
      Just pnd -> do


        let ptm = nodeTm pnd
        oldh <- hashTermEquiv undefined
        h <- hashTermEquiv ptm

        pr <- UnionFind.find $ nodeUF pnd
        let pr_ms = clsMembers pr
        modifyMutVar' pr_ms (del oldh pnd)

        HT.delete (nodesEquiv ?eqsat) ptm

        -- update patterns here?

        findTerm' ptm >>= \case
          Just (pnd', _) -> do
            -- TODO: does this need to go on a queue?
            do_merge pnd' pnd Congr
          Nothing -> do
            HT.insert (nodesEquiv ?eqsat) $ coerce prf
            addVector prf va
            modifyMutVar' pr_ms $ IntMap.alter (Just . (pnd:) . maybe [] id) h
    where
    del :: Int -> Node p -> IntMap [Node p] -> IntMap [Node p]
    del h x m = case filter (/= x) l of
        [] -> IntMap.delete h m
        l' -> IntMap.insert h l' m
     where Just l = m ^. at h



withEqSat :: (EqSat p => IO r) -> IO r
withEqSat f = do
  st <- EqSatState <$> HT.new <*> HT.new
  let ?eqsat = st
  f

testTm :: IO (Node p)
testTm = withEqSat $ do
  a <- makeTerm $ Term (Var 2) []
  b <- makeTerm $ Term (Var 3) []
  c <- makeTerm $ Term Add [a,b]
  d <- makeTerm $ Term (Var 1) []
  makeTerm $ Term Add [c,d]


-- class BuildTerm a where
--   buildTerm :: EqSat p => (TmHead, [a]) -> IO (Node p)

-- instance BuildTerm (Node p) where
--   buildTerm (hd, bd) = makeTerm $ Term hd bd
-- instance BuildTerm a => BuildTerm (TmHead, [a]) where
--   buildTerm a = buildTerm =<< traverse (traverse buildTerm) a


-- -- using IncoherentInstances to make build infer
-- class BuildTerm a => Buildable a
-- instance Buildable x => Buildable (TmHead, [x])
-- instance {-# INCOHERENT #-} a ~ Node p => Buildable a

-- build :: Buildable a => (TmHead, [a]) -> IO (Node p)
-- build x = withEqSat (buildTerm x)
