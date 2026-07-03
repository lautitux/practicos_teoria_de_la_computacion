module Chi where

import Data.Maybe

-- Sintaxis

data Expr
  = Var X
  | Cons K [Expr]
  | Lambda X Expr
  | Apl Expr Expr
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

instance Show Value where
  show (LambdaVal x e) = "\\" ++ x ++ "." ++ show e
  show (ConsVal "Nil" []) = "[]"
  show (ConsVal "Cons" [x, xs]) = "[" ++ show x ++ showList xs ++ "]"
    where
      showList (ConsVal "Nil" []) = ""
      showList (ConsVal "Cons" [x, xs]) = ", " ++ show x ++ showList xs
  show (ConsVal "O" []) = "0"
  show n@(ConsVal "S" [x]) = show $ toNat n
    where
      toNat (ConsVal "O" []) = 0
      toNat (ConsVal "S" [x]) = 1 + toNat x
  show (ConsVal "Pair" [a, b]) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (ConsVal k []) = k
  show (ConsVal k es) = k ++ " " ++ show es

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
efecto (Apl e1 e2) s = Apl (efecto e1 s) (efecto e2 s)
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
step (Apl e e') =
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

-- Utilidades

nil :: Expr
nil = Cons "Nil" []

k :: String -> [Expr] -> Expr
k = Cons

p :: (Expr, Expr) -> Expr
p (a, b) = Cons "Pair" [a, b]

true :: Expr
true = Cons "True" []

false :: Expr
false = Cons "False" []

infixr 5 #

(#) :: Expr -> Expr -> Expr
(#) v (Cons "Nil" []) = Cons "Cons" [v, Cons "Nil" []]
(#) v ls@(Cons "Cons" [x, xs]) = Cons "Cons" [v, ls]

natToChi :: Int -> Expr
natToChi 0 = Cons "O" []
natToChi x = Cons "S" [natToChi (x - 1)]
