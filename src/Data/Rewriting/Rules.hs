{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Rewrite rules
module Data.Rewriting.Rules where



import Data.Comp
import Data.Comp.Ops
import Data.Patch
import Data.Kind (Type)



----------------------------------------------------------------------------------------------------
-- * Tagless rewrite rules
----------------------------------------------------------------------------------------------------

-- | Rewrite rules
data Rule lhs rhs
  where
    Rule :: lhs a -> rhs a -> Rule lhs rhs

-- | Construct a rule from an LHS and an RHS
(===>) :: lhs a -> rhs a -> Rule lhs rhs
(===>) = Rule

infix 1 ===>

-- | Representations supporting wildcards
class WildCard r
  where
    __ :: r a

-- | Meta-variable applied to a number of 'Var' expressions
data MetaExp r a
  where
    MVar :: MetaRep r a -> MetaExp r a
    MApp :: MetaExp r (a -> b) -> MetaArg r a -> MetaExp r b

-- | Representations supporting meta-variables
class MetaVar r
  where
    -- Representation of meta-variable identifiers
    type MetaRep r :: Type -> Type
    type MetaArg r :: Type -> Type
    metaExp :: MetaExp r a -> r a

-- | Construct a meta-variable
meta :: MetaVar r => MetaRep r a -> r a
meta = metaExp . MVar

-- | Meta-variable application (used for all but the first and last variable)
($$) :: MetaExp r (a -> b) -> MetaArg r a -> MetaExp r b
($$) = MApp

-- | Meta-variable application (used for the last variable)
($-) :: MetaVar r => MetaExp r (a -> b) -> MetaArg r a -> r b
f $- a = metaExp (MApp f a)

-- | Meta-variable application (used for the first variable)
(-$) :: MetaRep r (a -> b) -> MetaArg r a -> MetaExp r b
f -$ a = MApp (MVar f) a

-- | Meta-variable application (used when there is only variable)
(-$-) :: MetaVar r => MetaRep r (a -> b) -> MetaArg r a -> r b
f -$- a = metaExp (MApp (MVar f) a)

infixl 2 $$, $-, -$, -$-

-- | Variable identifier
type Name = Integer

-- | Typed meta-variable identifiers
newtype MetaId a = MetaId Name
  deriving (Eq, Show, Ord, Num, Enum, Real, Integral)

-- | Rules that may take a number of meta-variables as arguments. Those meta-variables are
-- implicitly forall-quantified.
class Quantifiable rule
  where
    -- | Rule type after quantification
    type RuleType rule

    -- | Quantify a rule starting from the provided variable identifier
    quantify' :: Name -> rule -> RuleType rule

-- | Base case: no meta-variables
instance Quantifiable (Rule lhs rhs)
  where
    type RuleType (Rule lhs rhs) = Rule lhs rhs
    quantify' _ = id

-- | Recursive case: one more meta-variable
instance (Quantifiable rule, m ~ MetaId a) => Quantifiable (m -> rule)
  where
    type RuleType (m -> rule) = RuleType rule
    quantify' i rule = quantify' (i+1) (rule (MetaId i))

-- | Forall-quantify the meta-variable arguments of a rule
quantify :: (Quantifiable rule, RuleType rule ~ Rule lhs rhs) => rule -> Rule lhs rhs
quantify = quantify' 0



----------------------------------------------------------------------------------------------------
-- * Representation of rules
----------------------------------------------------------------------------------------------------

-- | Functor representing wildcards
data WILD a = WildCard
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | Functor representing meta variables applied to a number of 'Var' expressions
data META r a = forall b . Meta (MetaExp r b)

instance Functor     (META r) where fmap f (Meta m) = Meta m
instance Foldable    (META r) where foldr _ a _ = a
instance Traversable (META r) where traverse _ (Meta m) = pure (Meta m)

-- | Left hand side of a rule
newtype LHS f a = LHS { unLHS :: Term (WILD :+: META (LHS f) :+: f) }

-- | Right hand side of a rule
newtype RHS f a = RHS { unRHS :: Term (META (RHS f) :+: f) }

instance WildCard (LHS f)
  where
    __ = LHS $ Term $ Inl WildCard

-- | Representation of object variables
type family Var (r :: Type -> Type) :: Type -> Type

instance MetaVar (LHS f)
  where
    type MetaRep (LHS f) = MetaId
    type MetaArg (LHS f) = Var (LHS f)
    metaExp = LHS . Term . Inr . Inl . Meta

instance MetaVar (RHS f)
  where
    type MetaRep (RHS f) = MetaId
    type MetaArg (RHS f) = RHS f
    metaExp = RHS . Term . Inl . Meta



----------------------------------------------------------------------------------------------------
-- * Generalize over representations
----------------------------------------------------------------------------------------------------

class Rep r
  where
    type PF r :: Type -> Type
    toRep   :: Term (PF r) -> r a
    fromRep :: r a -> Term (PF r)

instance Rep (LHS f)
  where
    type PF (LHS f) = WILD :+: META (LHS f) :+: f
    toRep   = LHS
    fromRep = unLHS

instance Rep (RHS f)
  where
    type PF (RHS f) = META (RHS f) :+: f
    toRep   = RHS
    fromRep = unRHS



----------------------------------------------------------------------------------------------------
-- * Misc.
----------------------------------------------------------------------------------------------------

tRule :: Patch (Rule (LHS f) (RHS f)) (Rule (LHS f) (RHS f))
tRule = id

data A = A deriving (Eq)  -- Denoting a polymorphic type
data B = B deriving (Eq)  -- Denoting a polymorphic type
data C = C deriving (Eq)  -- Denoting a polymorphic type

tA :: Patch A A
tA = id

tB :: Patch B B
tB = id

tC :: Patch C C
tC = id

-- | Substitution
type Subst f = [(Name, Term f)]

