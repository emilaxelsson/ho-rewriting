{-# LANGUAGE TupleSections #-}

-- | First-order rewriting
module Data.Rewriting.FirstOrder where



import Control.Monad.Reader
import Control.Monad.Writer
import Data.Function (on)
import Data.List (groupBy)

import Data.Comp
import Data.Comp.Ops

import Data.Rewriting.Rules



-- | First-order matching. Results in a list of candidate mappings.
--
-- This function assumes that there are no applications of meta-variables in `LHS`.
matchM :: (Functor f, Foldable f, EqF f) => LHS f a -> Term f -> WriterT (Subst f) Maybe ()
matchM (LHS lhs) t = go lhs t
  where
    go (Term (Inl WildCard)) _                       = return ()
    go (Term (Inr (Inl (Meta (MVar (MetaId v)))))) t = tell [(v,t)]
    go (Term (Inr (Inr f))) (Term g)
      | Just subs <- eqMod f g                       = mapM_ (uncurry go) subs
    go _ _                                           = fail "No match"

-- | Check if all terms are equal, and if so, return one of them
solveTerm :: EqF f => [Term f] -> Maybe (Term f)
solveTerm (t:ts) = guard (all (==t) ts) >> return t
solveTerm _      = Nothing

-- | Turn a list of candidate mappings into a substitution. Succeeds iff. all mappings for the same
-- variable are equal.
solveSubst :: EqF f => [(Name, Term f)] -> Maybe (Subst f)
solveSubst s = sequence [fmap (v,) $ solveTerm ts | g <- gs, let (v:_,ts) = unzip g]
  where
    gs = groupBy ((==) `on` fst) s
      -- TODO Make O(n * log n)

-- | First-order matching. Succeeds if the pattern matches and all occurrences of a given
-- meta-variable are matched against equal terms.
--
-- This function assumes that there are no applications of meta-variables in `LHS`.
match :: (Functor f, Foldable f, EqF f) => LHS f a -> Term f -> Maybe (Subst f)
match lhs = solveSubst <=< execWriterT . matchM lhs

-- | Naive substitution. Succeeds iff. each meta-variable in 'RHS' has a mapping in the
-- substitution.
--
-- This function assumes that there are no applications of meta-variables in `RHS`.
substitute :: Traversable f => Subst f -> RHS f a -> Maybe (Term f)
substitute subst = cataM go . unRHS
  where
    go (Inl (Meta (MVar (MetaId v)))) = lookup v subst
    go (Inr f)                        = return (Term f)

-- | Apply a rule. Succeeds iff. both matching and substitution succeeds.
--
-- This function assumes that there are no applications of meta-variables in `LHS` or `RHS`.
rewrite :: (Traversable f, EqF f) => Rule (LHS f) (RHS f) -> Term f -> Maybe (Term f)
rewrite (Rule lhs rhs) t = do
    subst <- match lhs t
    substitute subst rhs

-- | Apply the first succeeding rule from a list of rules. If no rule succeeds the term is returned
-- unchanged.
--
-- This function assumes that there are no applications of meta-variables in `LHS` or `RHS`.
applyFirst :: (Traversable f, EqF f) => [Rule (LHS f) (RHS f)] -> Term f -> Term f
applyFirst rs t = case [t' | rule <- rs, Just t' <- [rewrite rule t]] of
    t':_ -> t'
    _    -> t

-- | Apply a list of rules bottom-up across a term
--
-- This function assumes that there are no applications of meta-variables in `LHS` or `RHS`.
bottomUp :: Functor f => (Term f -> Term f) -> Term f -> Term f
bottomUp rew = rew . Term . fmap (bottomUp rew) . unTerm

-- | Apply a list of rules top-down across a term
--
-- This function assumes that there are no applications of meta-variables in `LHS` or `RHS`.
topDown :: Functor f => (Term f -> Term f) -> Term f -> Term f
topDown rew = Term . fmap (topDown rew) . unTerm . rew

