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

module Feldspar where



import Data.Comp.Fixplate

import Data.Rewriting.Rules
import Data.Rewriting.FirstOrder hiding (applyFirst)
import Data.Rewriting.HigherOrder

import Simple



data FORLOOP a = ForLoop a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

deriveEq1 ''FORLOOP
deriveShow1 ''FORLOOP

instance EqF FORLOOP where equalF = defaultEqualF
instance ShowF FORLOOP where showsPrecF = defaultShowsPrecF

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

simplify :: Data a -> Data a
simplify = Data . rewriteWith (bottomUp (applyFirst app rulesFeld)) . unData

forExample :: Data Int -> Data Int
forExample a
    = forLoop a a (\i s -> (i-i)+s)
    + forLoop a a (\i s -> i*i+100)

drawForExample  = drawTermU $ unData $ lam forExample
drawForExampleR = drawTermU $ unData $ simplify $ lam forExample

feld1 :: Data Int -> Data Int
feld1 a = a + a + 3

drawFeld1  = drawTermU $ unData $ lam feld1
drawFeld1R = drawTermU $ unData $ simplify $ lam feld1

feld2 :: Data Int
feld2 = forLoop 0 0 (+)

drawFeld2  = drawTermU $ unData feld2
drawFeld2R = drawTermU $ unData $ simplify feld2

feld3 :: Data Int -> Data Int
feld3 a = forLoop a 0 (\i s -> a+i)

drawFeld3  = drawTermU $ unData $ lam feld3
drawFeld3R = drawTermU $ unData $ simplify $ lam feld3

feld4 :: Data Int -> Data Int
feld4 a = forLoop a 0 (\i s -> a + i + s) + forLoop a 0 (\i s -> a + i + s)

drawFeld4  = drawTermU $ unData $ lam feld4
drawFeld4R = drawTermU $ unData $ simplify $ lam feld4

