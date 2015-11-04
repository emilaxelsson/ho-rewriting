{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- Test that rule application does not lead to capturing

import System.Exit

import Data.Comp
-- import Data.Comp.Render
import Data.Patch
  -- Could use partial type signatures instead (on GHC >= 7.10)

import Data.Rewriting.Rules
import Data.Rewriting.FirstOrder hiding (applyFirst)
import Data.Rewriting.HigherOrder

import Feldspar

lamm :: (LAM :<: PF rep, Rep rep) => Name -> rep b -> rep (a -> b)
lamm v body = toRep $ inject $ Lam v $ fromRep body

dvar :: Name -> Data a
dvar = Data . inject . Var

rule_strange1 aa bb =
    meta aa + meta bb
      ===>
    forLoop 1 0 (\x y -> meta bb + var x + meta aa + var y)

-- Strange rule with a free variable on the RHS
rule_strange2 =
    __ - __
      ===>
    forLoop_ 1 0 (lamm 0 $ lamm 0 $ (var 0 + (var 1 -:: tCon tInt)))

simplify' :: Data a -> Data a
simplify' = Data . rewriteWith (bottomUp (applyFirst app rulesStrange)) . unData
  where
    rulesStrange =
      [ quantify (rule_strange1 -:: tCon tInt >-> id)
      , quantify (rule_strange2)
      ]

testFun1 :: Data (Int -> Int -> Int)
testFun1 = lam $ \v1 -> lam $ \v0 -> v1 + v0

testFun2 :: Data (Int -> Int -> Int)
testFun2 = lam $ \v1 -> lam $ \v0 -> v1 - v0

testFun1_simp_golden :: Data (Int -> Int -> Int)
testFun1_simp_golden =
    lamm 1 $ lamm 0 $ forLoop_ 1 0 $ lamm 2 $ lamm 3 $ dvar 0 + dvar 2 + dvar 1 + dvar 3

testFun2_simp_golden :: Data (Int -> Int -> Int)
testFun2_simp_golden =
    lamm 1 $ lamm 0 $ forLoop_ 1 0 $ lamm 0 $ lamm 2 $ dvar 2 + dvar 1

tests =
    [ unData (simplify' testFun1) == unData testFun1_simp_golden
    , unData (simplify' testFun2) == unData testFun2_simp_golden
    ]

main = if and tests
    then putStrLn "All tests passed"
    else do
      putStrLn $ "Tests " ++ show [i | (i,False) <- zip [0..] tests] ++ " failed"
      exitFailure


