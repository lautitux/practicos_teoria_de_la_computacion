module Chi where

import Control.Exception
import Data.Maybe

-- Sintaxis

data Expr
  = Var X
  | Cons K [Expr]
  | Lambda X Expr
  | Ap Expr Expr
  | Case Expr [Branch]
  | Rec X Expr
  deriving (Show)

type X = String

type K = String

type Branch = (K, ([X], Expr))

-- Semantica

data Value
  = ConsVal K [Value]
  | LambdaVal X Expr
  deriving (Show)

data Weak
  = WeakCons K [Expr]
  | WeakLambda X Expr

type Sigma = [(X, Expr)]

buscar :: X -> Sigma -> Expr
buscar x s =
  case lookup x s of
    Just e -> e
    Nothing -> Var x

bajar :: (Eq k) => k -> [(k, v)] -> [(k, v)]
bajar k = filter ((/= k) . fst)

bajarN :: (Eq k) => [k] -> [(k, v)] -> [(k, v)]
bajarN ks al = foldl (flip bajar) al ks

efecto :: Expr -> Sigma -> Expr
efecto (Var x) s = buscar x s
efecto (Cons k es) s = Cons k (map (`efecto` s) es)
efecto (Lambda x e) s = Lambda x (efecto e (bajar x s))
efecto (Ap e1 e2) s = Ap (efecto e1 s) (efecto e2 s)
efecto (Case e b) s =
  Case
    (efecto e s)
    ( map
        (\(k, (xs, e')) -> (k, (xs, efecto e' (bajarN xs s))))
        b
    )
efecto (Rec x e) s = Rec x (efecto e (bajar x s))

-- 4)
-- (x y)[x := (x y), y := (True [])]
-- Sustitucion multiple: ((x y) (True []))
-- Sustitucion simple iterada:
--  {Paso 1} ((x y) y)
--  {Paso 2} ((x (True [])) (True []))

step :: Expr -> Weak
step (Cons k es) = WeakCons k es
step (Lambda x e) = WeakLambda x e
step (Ap e e') =
  case step e of
    WeakCons k es -> WeakCons k (es ++ [e'])
    WeakLambda x e'' -> step (efecto e'' [(x, e')])
step (Case e bs) =
  case step e of
    WeakCons k es ->
      let (xs, e') = fromJust (lookup k bs)
       in case length xs == length es of
            True -> step (efecto e' (zip xs es))
step (Rec x e) = step (efecto e [(x, Rec x e)])

eval :: Expr -> Value
eval e =
  case step e of
    WeakLambda x e' -> LambdaVal x e'
    WeakCons k es -> ConsVal k (map eval es)

{- ORMOLU_DISABLE -}
-- 7)
-- OR =
-- \a.\b.case a of {
--      True -> [] True [];
--      False -> [] b;
-- }

or = Lambda "a" $ Lambda "b" $ Case (Var "a") [
    ("True", ([], Cons "True" [])),
    ("False", ([], Var "b"))
  ]

-- TRIPLE =
-- rec triple.\n.case n of {
--      O -> [] O [];
--      S -> [x] S [S [S [triple x]]];
-- }

triple = Rec "triple" $ Lambda "n" $ Case (Var "n") [
    ("O", ([], Cons "O" [])),
    ("S", (["x"], Cons "S" [Cons "S" [Cons "S" [Ap (Var "triple") (Var "x")]]]))
  ]

-- DUPLICAR =
-- rec duplicar.\ls.case ls of {
--    Nil -> [] Nil [];
--    Cons -> [x, xs] Cons [x, Cons [x, duplicar xs]];
-- }

duplicar = Rec "duplicar" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "Nil" [])),
    ("Cons", (["x", "xs"], Cons "Cons" [Var "x", Cons "Cons" [Var "x", Ap (Var "duplicar") (Var "xs")]]))
  ]

-- RAMAC =
-- rec ramaC.\t.case t of {
--    H -> [x] Cons [x, Nil []];
--    T -> [lt, ct, rt, x] Cons [x, ramaC ct];
-- }

ramaC = Rec "ramaC" $ Lambda "t" $ Case (Var "t") [
    ("H", (["x"], Cons "Cons" [Var "x", Cons "Nil" []])),
    ("T", (["lt", "ct", "rt", "x"], Cons "Cons" [Var "x", Ap (Var "ramaC") (Var "ct")]))
  ]

-- CEROS =
-- rec ceros.Cons [O [], ceros]

ceros = Rec "ceros" $ Cons "Cons" [Cons "O" [], Var "ceros"]

-- TAKES =
-- rec takes.\n.\ls.case ls of {
--     Nil -> [] Nil [];
--     Cons -> [x, xs] case n of {
--        O -> [] Nil [];
--        S -> [y] Cons [x, takes y xs];
--     };
-- }

takes = Rec "takes" $ Lambda "n" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "Nil" [])),
    ("Cons", (["x", "xs"], Case (Var "n") [
      ("O", ([], Cons "Nil" [])),
      ("S", (["y"], Cons "Cons" [Var "x", Ap (Ap (Var "takes") (Var "y")) (Var "xs")]))
    ]))
  ]
{- ORMOLU_ENABLE -}
