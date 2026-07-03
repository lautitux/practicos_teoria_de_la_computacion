module Practico0 where

import Data.List

-- Sintaxis

data Expr
  = Var X
  | EmptySet
  | UnitSet Z
  | Belongs Z Expr
  | Union Expr Expr
  | Inter Expr Expr
  | Diff Expr Expr
  | SubsetOf Expr Expr
  | Assign X Expr

type X = String

type Z = Int

-- Semantica

data Value
  = Set [Int]
  | Bool Bool
  deriving (Show)

type M = [(X, Value)]

eval :: M -> Expr -> (M, Value)
eval m (Var x) =
  case lookup x m of
    Just v -> (m, v)
    Nothing -> error ("La variable '" ++ x ++ "' no tiene ningun valor asignado.")
eval m EmptySet = (m, Set [])
eval m (UnitSet z) = (m, Set [z])
eval m (Belongs z e) = (m', Bool $ elem z c)
  where
    (m', c) = expectSet m e
eval m (Union e1 e2) = (m'', Set $ union c1 c2)
  where
    (m', c1) = expectSet m e1
    (m'', c2) = expectSet m' e2
eval m (Inter e1 e2) = (m'', Set $ intersect c1 c2)
  where
    (m', c1) = expectSet m e1
    (m'', c2) = expectSet m' e2
eval m (Diff e1 e2) = (m'', Set $ difference c1 c2)
  where
    (m', c1) = expectSet m e1
    (m'', c2) = expectSet m' e2
eval m (SubsetOf e1 e2) = (m'', Bool $ included c1 c2)
  where
    (m', c1) = expectSet m e1
    (m'', c2) = expectSet m' e2
eval m (Assign x e) = ((x, v) : m', v)
  where
    (m', v) = eval m e

expectSet :: M -> Expr -> (M, [Int])
expectSet m e =
  case eval m e of
    (m', Set c) -> (m', c)
    _ -> error "Esperaba un conjunto pero obtuve un bool."

difference :: [Int] -> [Int] -> [Int]
difference c1 c2 = filter (not . (`elem` c2)) c1

isContained :: (Eq a) => [a] -> [a] -> Bool
isContained [] _ = True
isContained (x : xs) ls
  | x `elem` ls = xs `isContained` ls
  | otherwise = False

included :: [Int] -> [Int] -> Bool
included c1 c2 = c1 `isContained` c2

-- Definiciones dentro del lenguaje

conj1 = UnitSet 1 `Union` UnitSet 2 `Union` UnitSet 3

conj2 = UnitSet 2 `Union` UnitSet 3 `Union` UnitSet 4

conj3 = conj1 `Union` conj2

conj4 = conj1 `Inter` conj2

pert1 = 2 `Belongs` conj1

pert2 = 3 `Belongs` conj4

incl1 = conj1 `SubsetOf` conj2

incl2 = conj4 `SubsetOf` conj2

incl3 = conj1 `SubsetOf` conj3

ass1 = "w" `Assign` conj1

ass2 = "x" `Assign` conj4

ass3 = "y" `Assign` pert2

ass4 = "z" `Assign` incl2
