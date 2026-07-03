module Parte2 where

import Data.List

-- Ejercicio 1: Representación de términos

data Expr
  = Var X
  | Abs X Expr
  | Apl Expr Expr
  deriving (Eq)

type X = String

-- Ejercicio 2: Variables libres

freeVars :: Expr -> [X]
freeVars (Var x) = [x]
freeVars (Abs x e) = x `delete` freeVars e
freeVars (Apl e e') = freeVars e `union` freeVars e'

-- Ejercicio 3: Sustitución captura-evitante

freshName :: X -> [X] -> X
freshName x forbbiden
  | x `elem` forbbiden = freshName (x ++ "'") forbbiden
  | otherwise = x

-- e[x := n]
substitute :: X -> Expr -> Expr -> Expr
substitute x n (Var y)
  | x == y = n
  | otherwise = Var y
substitute x n (Apl e1 e2) = Apl (substitute x n e1) (substitute x n e2)
substitute x n (Abs y e)
  | x == y = Abs y e
  | y `elem` freeVars n =
      let y' = freshName y (x : freeVars n ++ freeVars e)
          e' = substitute y (Var y') e
       in Abs y' (substitute x n e')
  | otherwise = Abs y (substitute x n e)

-- Ejercicio 4: Semántica operacional
-- La formalización de las reglas se encuentra en el informe

step :: Expr -> Maybe Expr
step (Var _) = Nothing
step (Abs x e) = Nothing
step (Apl (Abs x e) v@(Abs _ _)) = Just (substitute x v e)
step (Apl v@(Abs _ _) e) = do
  e' <- step e
  return (Apl v e')
step (Apl e1 e2) = do
  e1' <- step e1
  return (Apl e1' e2)

-- Ejercicio 5: Evaluación completa

eval :: Expr -> Expr
eval v@(Abs _ _) = v
eval e = maybe e eval (step e)

-- Ejercicio 6: Pretty printer

pretty :: Expr -> String
pretty (Var x) = x
pretty (Abs x e) = "\\" ++ x ++ "." ++ pretty e
pretty (Apl e1 e2) = protectLeft e1 ++ " " ++ protectRight e2
  where
    protectLeft (Abs x e) = "(" ++ pretty (Abs x e) ++ ")"
    protectLeft e = pretty e

    protectRight (Var x) = x
    protectRight e = "(" ++ pretty e ++ ")"

instance Show Expr where
  show = pretty

-- Ejercicio 7: Sharing

-- Ejercicio 8: Numerales de Church

-- zero = \f.\x.x
zeroC :: Expr
zeroC = Abs "f" $ Abs "x" (Var "x")

-- one = \f.\x.f x
oneC :: Expr
oneC = Abs "f" $ Abs "x" (Var "f" `Apl` Var "x")

-- two = \f.\x.f (f x)
twoC :: Expr
twoC = Abs "f" $ Abs "x" (Var "f" `Apl` (Var "f" `Apl` Var "x"))

-- succ = \n.\f.\x.f (n f x)
succC :: Expr
succC = Abs "n" $ Abs "f" $ Abs "x" (Var "f" `Apl` (Var "n" `Apl` Var "f" `Apl` Var "x"))

-- sum = \m.\n.\f.\x.m f (n f x)
sumC :: Expr
sumC = Abs "m" $ Abs "n" $ Abs "f" $ Abs "x" (Var "m" `Apl` Var "f" `Apl` (Var "n" `Apl` Var "f" `Apl` Var "x"))

-- mult = \m.\n.\f.\x.m (n f) x
multC :: Expr
multC = Abs "m" $ Abs "n" $ Abs "f" $ Abs "x" (Var "m" `Apl` (Var "n" `Apl` Var "f") `Apl` Var "x")

-- Ejemplo 1: Evaluar el número 0 de Church directamente
-- Resultado: \f.\x.x
ejemploZeroC :: Expr
ejemploZeroC = eval zeroC

-- Ejemplo 2: El sucesor de 1 (debería dar el numeral de Church para 2)
-- Resultado: \f.\x.f ((\f.\x.f x) f x)
-- Comentario: Aplicando dos β-reduccion queda \f.\x.f (f x), la forma normal
--             anterior se debe a la semantica CBV. Lo mismo aplica a
--             los siguientes casos.
ejemploSuccC :: Expr
ejemploSuccC = eval (Apl succC oneC)

-- Ejemplo 3: Sumar 1 + 2 (debería dar el numeral de Church para 3)
-- Resultado: \f.\x.(\f.\x.f x) f ((\f.\x.f (f x)) f x)
-- Comentario: Aplicando cuatro β-reduccion queda \f.\x.f (f (f x))
ejemploSumC :: Expr
ejemploSumC = eval (Apl (Apl sumC oneC) twoC)

-- Ejemplo 4: Multiplicar 2 * 1 (debería dar el numeral de Church para 2)
-- Resultado: \f.\x.(\f.\x.f (f x)) ((\f.\x.f x) f) x
-- Comentario: Aplicando seis β-reduccion queda \f.\x.f (f x)
ejemploMultC :: Expr
ejemploMultC = eval (Apl (Apl multC twoC) oneC)

-- Ejemplo 5: Una combinación: Sucesor de (0 + 1) -> Sucesor de 1 -> 2
-- Resultado: \f.\x.f ((\f.\x.(\f.\x.x) f ((\f.\x.f x) f x)) f x)
-- Comentario: Aplicando seis β-reduccion se alcanza la forma normal \f.\x.f (f x).
ejemploCompuestoC :: Expr
ejemploCompuestoC = eval (Apl succC (Apl (Apl sumC zeroC) oneC))

-- Ejercicio 9: Comparación experimental