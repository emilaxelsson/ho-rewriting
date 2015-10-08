{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Simple where



import Data.Comp
import Data.Comp.Derive
import Data.Comp.Render
import Data.Patch
  -- Could use partial type signatures instead (on GHC >= 7.10)

import Data.Rewriting.Rules
import Data.Rewriting.FirstOrder



-- Using the `Num` class as a tagless DSL:

-- 0 + x  ===>  x
rule_add1 x = 0 + meta x  ===>  meta x

-- x + x  ===>  x*2
rule_add2 x = meta x + meta x  ===>  meta x * 2

-- x - x  ===>  0
rule_sub x = meta x - meta x  ===>  0

-- 0 * x  ===>  0
rule_mul = 0 * __  ===>  (0 -:: tCon tInteger)
  -- Rules cannot be polymorphic

-- Adding language constructs for "logic" expressions:

class Logic r
  where
    false :: r Bool
    true  :: r Bool
    noT   :: r Bool -> r Bool
    (<&>) :: r Bool -> r Bool -> r Bool
    (===) :: Eq a => r a -> r a -> r Bool
    cond  :: r Bool -> r a -> r a -> r a

-- not (not x)  ===>  x
rule_not x = noT (noT (meta x))  ===>  meta x

-- false <&> x  ===>  false
rule_and x = false <&> meta x  ===>  false

-- x === x  ===>  true
rule_eq x = meta x === meta x  ===>  true

-- cond _ tf tf  ===>  tf
rule_cond1 tf = cond __ (meta tf) (meta tf)  ===>  meta tf

-- cond (not c) t f  ===>  cond c f t
rule_cond2 c t f = cond (noT (meta c)) (meta t) (meta f)  ===>  cond (meta c) (meta f) (meta t)

data NUM a
    = Num Integer
    | Add a a
    | Sub a a
    | Mul a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''NUM]

instance Render NUM

data LOGIC a
    = Bool Bool
    | Not a
    | And a a
    | Equal a a
    | Cond a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''LOGIC]

instance Render LOGIC

type Lang = NUM :+: LOGIC

newtype Expr a = Expr { unExpr :: Term Lang }
  deriving (Eq, Show)

instance Rep Expr
  where
    type PF Expr = Lang
    toRep   = Expr
    fromRep = unExpr

instance (NUM :<: f) => Num (Term f)
  where
    fromInteger = inject . Num
    a + b       = inject $ Add a b
    a - b       = inject $ Sub a b
    a * b       = inject $ Mul a b

deriving instance Num a => Num (Expr a)

deriving instance (NUM :<: PF (LHS f), Num a) => Num (LHS f a)
deriving instance (NUM :<: PF (RHS f), Num a) => Num (RHS f a)

instance (Rep r, LOGIC :<: PF r) => Logic r
  where
    false      = toRep $ inject (Bool False)
    true       = toRep $ inject (Bool True)
    noT        = toRep . inject . Not . fromRep
    a <&> b    = toRep $ inject $ And (fromRep a) (fromRep b)
    a === b    = toRep $ inject $ Equal (fromRep a) (fromRep b)
    cond c t f = toRep $ inject $ Cond (fromRep c) (fromRep t) (fromRep f)

rules =
    [ quantify rule_add1
    , quantify rule_add2
    , quantify rule_sub
    , quantify rule_mul
    , quantify rule_and
    , quantify (rule_eq -:: tCon tA >-> tRule)
    , quantify rule_cond1
    , quantify rule_cond2
    ]

expr1 :: Expr Integer
expr1 = 0 + 4

draw1  = drawTerm $ unExpr expr1
draw1R = drawTerm $ bottomUp (applyFirst rules) (unExpr expr1)

expr2 :: Expr Integer
expr2 = (5 + 5 + 3) + (0 + 4)

draw2  = drawTerm $ unExpr expr2
draw2R = drawTerm $ bottomUp (applyFirst rules) (unExpr expr2)

expr3 :: Expr Integer
expr3 = cond (0 === 1) (5+5) (5*2)

draw3  = drawTerm $ unExpr expr3
draw3R = drawTerm $ bottomUp (applyFirst rules) (unExpr expr3)

