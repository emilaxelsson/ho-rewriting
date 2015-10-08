{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Render

import Data.Rewriting.Rules
import Data.Rewriting.HigherOrder

import Simple



main = return () -- For `cabal test`

data FORLOOP a = ForLoop a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

derive [makeEqF, makeShowF, makeShowConstr] [''FORLOOP]

instance Render FORLOOP

type Feld = VAR :+: LAM :+: APP :+: NUM :+: LOGIC :+: FORLOOP

newtype Data a = Data { unData :: Term Feld }
  deriving (Eq, Show)

instance Rep Data
  where
    type PF Data = Feld
    toRep   = Data
    fromRep = unData

type instance Var Data = Data

instance Bind Data
  where
    var = id
    lam = mkLam (Data . inject . Var . toInteger)

deriving instance Num a => Num (Data a)

class ForLoop r
  where
    forLoop_ :: r Int -> r s -> r (Int -> s -> s) -> r s

instance (Rep r, FORLOOP :<: PF r) => ForLoop r
  where
    forLoop_ len init step = toRep $ inject $ ForLoop (fromRep len) (fromRep init) (fromRep step)

forLoop :: (ForLoop r, Bind r) => r Int -> r s -> (Var r Int -> Var r s -> r s) -> r s
forLoop len init body = forLoop_ len init (lam $ \i -> lam $ \s -> body i s)

-- forLoop 0 init _  ===>  init
rule_for1 init = forLoop 0 (meta init) (\i s -> __)  ===>  meta init

-- forLoop 0 init (\i s -> s)  ===>  init
rule_for2 init = forLoop __ (meta init) (\i s -> var s)  ===>  meta init

rule_for3 len init body =
    forLoop (meta len) (meta init) (\i s -> body -$- i)
      ===>
    cond (meta len === 0) (meta init) (body -$- (meta len - 1))

rulesFeld = rules ++
    [ quantify rule_for1
    , quantify rule_for2
    , quantify rule_for3
    ]

stripAnn :: Functor f => Term (f :&: a) -> Term f
stripAnn = cata (\(f :&: _) -> Term f)

simplify :: Data a -> Data a
simplify = Data . stripAnn . bottomUp (applyFirst app rulesFeld) . unData

forExample :: Data Int -> Data Int
forExample a
    = forLoop a a (\i s -> (i-i)+s)
    + forLoop a a (\i s -> i*i+100)

drawForExample  = drawTerm $ unData $ lam forExample
drawForExampleR = drawTerm $ unData $ simplify $ lam forExample

feld1 :: Data Int -> Data Int
feld1 a = a + a + 3

drawFeld1  = drawTerm $ unData $ lam feld1
drawFeld1R = drawTerm $ unData $ simplify $ lam feld1

feld2 :: Data Int
feld2 = forLoop 0 0 (+)

drawFeld2  = drawTerm $ unData feld2
drawFeld2R = drawTerm $ unData $ simplify feld2

feld3 :: Data Int -> Data Int
feld3 a = forLoop a 0 (\i s -> a+i)

drawFeld3  = drawTerm $ unData $ lam feld3
drawFeld3R = drawTerm $ unData $ simplify $ lam feld3

feld4 :: Data Int -> Data Int
feld4 a = forLoop a 0 (\i s -> a + i + s) + forLoop a 0 (\i s -> a + i + s)

drawFeld4  = drawTerm $ unData $ lam feld4
drawFeld4R = drawTerm $ unData $ simplify $ lam feld4

