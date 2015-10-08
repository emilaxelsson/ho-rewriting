{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Higher-order rewriting
module Data.Rewriting.HigherOrder where



import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.List (groupBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Ops
import Data.Comp.Render

import Data.Rewriting.Rules



-- | Representations supporting variable binding
class Bind r
  where
    var :: Var r a -> r a
    lam :: (Var r a -> r b) -> r (a -> b)

-- | Functor representing object variables
newtype VAR a = Var Name
  deriving (Eq, Show, Ord, Num, Enum, Real, Integral, Functor, Foldable, Traversable)

-- | Functor representing lambda abstraction
data LAM a = Lam Name a
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Functor representing application
data APP a = App a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''VAR]
derive [makeEqF, makeShowF, makeShowConstr] [''LAM]
derive [makeEqF, makeShowF, makeShowConstr] [''APP]

instance Render VAR
instance Render LAM
instance Render APP

fresh :: (LAM :<: f, Functor f, Foldable f) => Term f -> Name
fresh f
    | Just (Lam v _) <- project f = v+1
    | otherwise = maximum $ (0:) $ Foldable.toList $ fmap fresh $ unTerm f

-- | Generic lambda abstraction
mkLam
    :: (Rep r, VAR :<: PF r, LAM :<: PF r, Functor (PF r), Foldable (PF r))
    => (VAR a -> Var r a) -> (Var r a -> r b) -> r (a -> b)
mkLam mkVar f = toRep $ inject $ Lam v $ fromRep body
  where
    body = f (mkVar $ Var v)
    v    = fresh (fromRep body)

-- | Application operator, to use as argument to functions like 'applyFirst', 'bottomUp', etc.
app :: (APP :<: f) => Term (f :&: Set Name) -> Term (f :&: Set Name) -> Term (f :&: Set Name)
app f@(Term (_ :&: fv)) a@(Term (_ :&: av)) = Term (inj (App f a) :&: Set.union fv av)

type instance Var (LHS f) = VAR
type instance Var (RHS f) = VAR

instance (VAR :<: PF (LHS f), LAM :<: PF (LHS f), Functor f, Foldable f) =>
    Bind (LHS f)
  where
    var = LHS . inject . Var . toInteger
    lam = mkLam id

instance (VAR :<: PF (RHS f), LAM :<: PF (RHS f), Functor f, Foldable f) =>
    Bind (RHS f)
  where
    var = RHS . inject . Var . toInteger
    lam = mkLam id

-- | One-to-one map
type OneToOne a b = (Map a b, Map b a)

-- | Empty one-to-one map
oEmpty :: OneToOne a b
oEmpty = (Map.empty, Map.empty)

-- | Test if a mapping is in a one-to-one map
oMember :: (Ord a, Ord b) => (a,b) -> OneToOne a b -> Bool
oMember (a,b) (ab,_) = case Map.lookup a ab of
    Just b' -> b == b'
    Nothing -> False

-- | Test if either side of a mapping is in a one-to-one map
oMemberEither :: (Ord a, Ord b) => (a,b) -> OneToOne a b -> Bool
oMemberEither (a,b) (ab,ba) = Map.member a ab || Map.member b ba

-- | Left lookup in a one-to-one map
oLookupL :: Ord a => a -> OneToOne a b -> Maybe b
oLookupL a (ab,_) = Map.lookup a ab

-- | Insert a one-to-one mapping
oInsert :: (Ord a, Ord b) => (a,b) -> OneToOne a b -> OneToOne a b
oInsert (a,b) (ab,ba) = (Map.insert a b ab', Map.insert b a ba')
  where
    ab' = case Map.lookup b ba of
      Just a' -> Map.delete a' ab
      Nothing -> ab
    ba' = case Map.lookup a ab of
      Just b' -> Map.delete b' ba
      Nothing -> ba

getAnn :: Term (f :&: a) -> a
getAnn (Term (_ :&: a)) = a

-- | Environment keeping track of alpha-renaming
type AlphaEnv = OneToOne Name {-pattern-} Name {-term-}

-- | Higher-order matching. Results in a list of candidate mappings.
matchM :: forall f a
    .  ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS f)
       , LAM :<: PF (LHS f)
       , Functor f, Foldable f, EqF f
       )
    => LHS f a
    -> Term (f :&: Set Name)
    -> ReaderT AlphaEnv (WriterT (Subst (f :&: Set Name)) Maybe) ()
matchM (LHS lhs) t = go lhs t
  where
    go (Term (Inl WildCard)) _ = return ()

    go (Term (Inr (Inl (Meta mv)))) t = ReaderT $ \env -> goo env mv t
      where
        goo :: AlphaEnv
            -> MetaExp (LHS f) b
            -> Term (f :&: Set Name)
            -> WriterT (Subst (f :&: Set Name)) Maybe ()
        goo env (MVar (MetaId m)) t
            | Set.null (Set.intersection boundInPatt freeIn_t) = tell [(m,t)]
            | otherwise = fail "Variables would escape"
          where
            boundInPatt = Map.keysSet $ snd env
            freeIn_t    = getAnn t
        goo env (MApp mv (Var v)) t = do
          let Just w = oLookupL v env
                -- Lookup failure is a bug rather than a matching failure
          goo env mv (Term (inj (Lam w t) :&: Set.delete w (getAnn t)))

    go p (Term (g :&: _))
      | Just (Var v) <- project p
      , Just (Var w) <- proj g
      = do
          env <- ask
          guard ((v,w) `oMember` env)
            -- Rules should be closed, so `w` can't be free

    go p (Term (g :&: _))
      | Just (Lam v a) <- project p
      , Just (Lam w b) <- proj g
      = local (oInsert (v,w)) $ go a b

    go (Term (Inr (Inr f))) (Term (g :&: _))
      | Just subs <- eqMod f g
      = mapM_ (uncurry go) subs

    go _ _ = fail "No match"

-- | Alpha-equivalence
alphaEq :: (VAR :<: f, LAM :<: f, Functor f, Foldable f, EqF f) => Term f -> Term f -> Bool
alphaEq a b = runReader (go a b) oEmpty
  where
    go t u
      | Just (Var v) <- project t
      , Just (Var w) <- project u
      = reader $ \env -> oMember (v,w) env || (not (oMemberEither (v,w) env) && v==w)
    go t u
      | Just (Lam v a) <- project t
      , Just (Lam w b) <- project u
      = local (oInsert (v,w)) $ go a b
    go (Term f) (Term g)
      | Just subs <- eqMod f g
      = fmap and $ mapM (uncurry go) subs
    go _ _ = return False

-- | Check if all terms are alpha-equivalent, and if so, return one of them
solveTermAlpha :: (VAR :<: f, LAM :<: f, Functor f, Foldable f, EqF f) =>
    [Term (f :&: a)] -> Maybe (Term (f :&: a))
solveTermAlpha (t:ts) = guard (all (alphaEq (stripA t)) (map stripA ts)) >> return t
solveTermAlpha _      = Nothing

-- | Turn a list of candidate mappings into a substitution. Succeeds iff. all mappings for the same
-- variable are alpha-equivalent.
solveSubstAlpha :: (VAR :<: f, LAM :<: f, Functor f, Foldable f, EqF f) =>
    Subst (f :&: a) -> Maybe (Subst (f :&: a))
solveSubstAlpha s = sequence [fmap (v,) $ solveTermAlpha ts | g <- gs, let (v:_,ts) = unzip g]
  where
    gs = groupBy ((==) `on` fst) s
      -- TODO Make O(n * log n)

-- | Higher-order matching. Succeeds if the pattern matches and all occurrences of a given
-- meta-variable are matched against equal terms.
match
    :: ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS f)
       , LAM :<: PF (LHS f)
       , Functor f, Foldable f, EqF f
       )
    => LHS f a -> Term (f :&: Set Name) -> Maybe (Subst (f :&: Set Name))
match lhs = solveSubstAlpha <=< execWriterT . flip runReaderT oEmpty . matchM lhs

-- | Annotate a node with its set of free variables
annFreeVars :: (VAR :<: f, LAM :<: f, Functor f, Foldable f) =>
    f (Term (f :&: Set Name)) -> Term (f :&: Set Name)
annFreeVars f
    | Just (Var v) <- proj f = Term (inj (Var v) :&: Set.singleton v)
annFreeVars f
    | Just (Lam v a) <- proj f
    = Term (inj (Lam v a) :&: Set.delete v (getAnn a))
annFreeVars f = Term (f :&: Foldable.foldMap getAnn f)

-- | Capture-avoiding substitution. Succeeds iff. each meta-variable in 'RHS' has a mapping in the
-- substitution.
substitute :: forall f g a
    .  ( VAR :<: f
       , LAM :<: f
       , Traversable f
       , g ~ (f :&: Set Name)
       )
    => (Term g -> Term g -> Term g)  -- ^ Application operator
    -> Subst g
    -> RHS f a
    -> Maybe (Term g)
substitute app subst = cataM go . unRHS
  where
    go :: PF (RHS f) (Term g) -> Maybe (Term g)
    go (Inl (Meta mv)) = goo mv
      where
        goo :: MetaExp (RHS f) b -> Maybe (Term g)
        goo (MVar (MetaId v)) = lookup v subst
        goo (MApp mv t)       = liftM2 app (goo mv) $ cataM go (unRHS t)
    go (Inr f) = return $ annFreeVars f
  -- TODO Should avoid capturing

-- | Prepare a term for rewriting by annotating each node with its set of free
-- variables
prepare :: (VAR :<: f, LAM :<: f, Functor f, Foldable f) => Term f -> Term (f :&: Set Name)
prepare = cata annFreeVars

-- | Strip out the annotations from a term
stripAnn :: Functor f => Term (f :&: a) -> Term f
stripAnn = cata (\(f :&: _) -> Term f)

-- | Apply a higher-order rewriter to a term
withRewriter
    :: ( VAR :<: f
       , LAM :<: f
       , Functor f
       , Foldable f
       , g ~ (f :&: Set Name)
       )
    => (Term g -> Term g) -> Term f -> Term f
withRewriter rew = stripAnn . rew . prepare

-- | Apply a rule. Succeeds iff. both matching and substitution succeeds.
rewrite
    :: ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS f)
       , LAM :<: PF (LHS f)
       , Traversable f, EqF f
       , g ~ (f :&: Set Name)
       )
    => (Term g -> Term g -> Term g)  -- ^ Application operator
    -> Rule (LHS f) (RHS f)
    -> Term g
    -> Maybe (Term g)
rewrite app (Rule lhs rhs) t = do
    subst <- match lhs t
    substitute app subst rhs

-- | Apply the first succeeding rule from a list of rules. If no rule succeeds the term is returned
-- unchanged.
applyFirst
    :: ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS f)
       , LAM :<: PF (LHS f)
       , Traversable f, EqF f
       , g ~ (f :&: Set Name)
       )
    => (Term g -> Term g -> Term g)  -- ^ Application operator
    -> [Rule (LHS f) (RHS f)]
    -> Term g
    -> Term g
applyFirst app rs t = case [t' | r <- rs, Just t' <- [rewrite app r t]] of
    t':_ -> t'
    _    -> t

-- | Apply a list of rules bottom-up across a term
bottomUp
    :: ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS f)
       , LAM :<: PF (LHS f)
       , Functor f, Foldable f, EqF f
       , g ~ (f :&: Set Name)
       )
    => (Term g -> Term g)  -- ^ Node rewriter
    -> Term g
    -> Term g
bottomUp rew = rew . Term . fmap (bottomUp rew) . unTerm

