module Imp where

-- Syntax

data Program
  = Comp Program Program
  | Assign [X] [Expr]
  | Local [X] Program
  | Case X [Branch]
  | While X [Branch]

data Expr = Cons C [Expr] | Var X

type C = String

type X = String

type Branch = (C, ([X], Program))

-- Semantic

data Value
  = ConsVal C [Value]
  | Null
  deriving (Show)

valueToExpr :: Value -> Expr
valueToExpr (ConsVal c vs) = Cons c (map valueToExpr vs)

type Mem = [(X, Value)]

update :: (Eq a) => a -> b -> [(a, b)] -> [(a, b)]
update k v [] = [(k, v)]
update k v ((x, y) : xs)
  | k == x = (x, v) : xs
  | otherwise = (x, y) : update k v xs

delete :: (Eq a) => a -> [(a, b)] -> [(a, b)]
delete _ [] = []
delete k ((x, v) : xs)
  | k == x = xs
  | otherwise = (x, v) : delete k xs

updateAll :: (Eq a) => [a] -> [b] -> [(a, b)] -> [(a, b)]
updateAll ks vs al = foldl (\acc (k, v) -> update k v acc) al (zip ks vs)

deleteAll :: (Eq a) => [a] -> [(a, b)] -> [(a, b)]
deleteAll ks al = foldl (flip delete) al ks

-- e =M=> v
eval :: Mem -> Expr -> Value
eval m (Var x) =
  case lookup x m of
    Just (ConsVal c vs) -> ConsVal c vs -- Not Null
eval m (Cons c es) = ConsVal c (map (eval m) es)

-- M |> p |> M'
exec :: Mem -> Program -> Mem
-- x := e
exec m (Assign xs es) =
  if length xs == length es
    then
      updateAll xs (map (eval m) es) m
    else
      error "Mismatched amount of variables and values to assign."
-- local x p
exec m (Local xs p) = deleteAll xs $ exec ([(x, Null) | x <- xs] ++ m) p
-- p1 ; p2
exec m (Comp p1 p2) = exec m' p2
  where
    m' = exec m p1
-- case x of [b]
exec m (Case x bs) = exec m (Local xs (Comp (Assign xs (map valueToExpr vs)) p))
  where
    (ConsVal c vs) = eval m (Var x)
    (xs, p) = case lookup c bs of Just b -> b -- (buscar rama)
    -- while x of [b]
exec m (While x bs) =
  case lookup c bs of -- (buscar rama)
    Just (xs, p) -> exec m (Comp (Case x bs) (While x bs))
    Nothing -> m
  where
    (ConsVal c _) = eval m (Var x)

intToSuccessor :: Int -> Value
intToSuccessor 0 = ConsVal "0" []
intToSuccessor x = ConsVal "S" [intToSuccessor (x - 1)]

-- Programas en Imp

{- ORMOLU_DISABLE -}
notP :: X -> Program
notP b = Case b [
    ("True", ([], Assign ["result"] [Cons "False" []])),
    ("False", ([], Assign ["result"] [Cons "True" []]))
  ]

parP :: X -> Program
parP n = Local ["n'", "par"] (
  Assign ["n'", "par"] [Var n, Cons "True" []] `Comp`
  While "n'" [
    ("S", (["x"], Assign ["n'"] [Var "x"] `Comp`
                  notP "par" `Comp`
                  Assign ["par"] [Var "result"]))
  ] `Comp`
  Assign ["result"] [Var "par"])

-- sumaP =
-- local m' n' {
--    m', n' := m, n;
--    while n' is {
--       S [x] -> m', n' := S [m], x
--    };
--    result := m'
-- }

sumaP :: X -> X -> Program
sumaP m n = Local ["m'", "n'"] (
  Assign ["m'", "n'"] [Var m, Var n] `Comp`
  While "n'" [
    ("S", (["x"], Assign ["m'", "n'"] [Cons "S" [Var "m'"], Var "x"]))
  ] `Comp`
  Assign ["result"] [Var "m'"])
{- ORMOLU_ENABLE -}
