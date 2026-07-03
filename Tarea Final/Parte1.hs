module Parte1 where

import Chi
import Data.List (delete, elemIndex, find, nub, nubBy, permutations)

-- 1.1 Representacion de dominios y soluciones (PROBLEMA A)

data Literal = LVar String | Neg String

type DomA = [[Literal]]

type SolA = [(String, Bool)]

-- 1.2 Verificadores en tiempo polinomial (PROBLEMA A)

verifyA :: (DomA, SolA) -> Bool
verifyA (dom, sol) =
  case substitute dom sol of
    Just ss -> all or ss
    Nothing -> False
  where
    substitute :: DomA -> SolA -> Maybe [[Bool]]
    substitute dom sol = mapM (substituteList sol) dom

    substituteList :: SolA -> [Literal] -> Maybe [Bool]
    substituteList sol ls = mapM (getVal sol) ls

    getVal :: SolA -> Literal -> Maybe Bool
    getVal sol (LVar v) = lookup v sol
    getVal sol (Neg v) = fmap not (lookup v sol)

{-
    JUSTIFICACIÓN DE ORDEN (verifyA):

    Sea n = cantidad de cláusulas, l = longitud máxima de una cláusula
    (cantidad de literales), v = cantidad de variables (tamaño de 'sol').

    - lookup v sol             -> O(v)            (búsqueda lineal en la lista de asignación)
    - getVal sol lit           -> O(v)            (lookup + a lo sumo un 'not', O(1))
    - substituteList sol ls    -> O(l * v)        (mapM aplica getVal a cada literal de la cláusula)
    - substitute dom sol       -> O(n * l * v)    (mapM aplica substituteList a cada una de las n cláusulas)
    - all or ss                -> O(n * l)        (recorre n listas de hasta l booleanos)

    Total: O(n*l*v + n*l) = O(n * l * v)

    Como n, l y v están acotados por el tamaño de la entrada (la fórmula y la
    asignación), esta cota es POLINOMIAL en el tamaño de la entrada (en el peor
    caso, cúbica si n ≈ l ≈ v).
-}

-- 1.3 Resolucion en tiempo exponencial (PROBLEMA A)

solveA :: DomA -> SolA
solveA dom =
  case find (\sol -> verifyA (dom, sol)) tv of
    Just sol -> sol
    Nothing -> error "Formula no satisfacible"
  where
    vars = nub $ map var (concat dom)
    tv = map (zip vars) (mapM (const [True, False]) vars)

    var (LVar x) = x
    var (Neg x) = x

{-
    JUSTIFICACIÓN DE ORDEN (solveA):

    Sea n = cantidad de cláusulas, l = longitud máxima de una cláusula
    (cantidad de literales), v = cantidad de variables (tamaño de 'sol').

    vars tiene v variables distintas.
    tv genera TODAS las asignaciones posibles: 2^v asignaciones (tabla de verdad completa).

    Para cada una de las 2^v asignaciones, 'find' evalúa verifyA, que es O(nlv).

    Total: O(2^v * n * l * v)

    Es EXPONENCIAL en la cantidad de variables v.
-}

-- 1.4 Ejemplos Haskell (PROBLEMA A)

-- (p ∨ ¬q ∨ r) ∧ (¬p ∨ q ∨ r) ∧ (q ∨ r)
ejemploSAT :: DomA
ejemploSAT =
  [ [LVar "p", Neg "q", LVar "r"],
    [Neg "p", LVar "q", LVar "r"],
    [LVar "q", LVar "r"]
  ]

solucionValidaSAT :: SolA
solucionValidaSAT = [("p", True), ("q", True), ("r", True)]

pruebaVerifyTrueSAT :: Bool
pruebaVerifyTrueSAT = verifyA (ejemploSAT, solucionValidaSAT)

{-
    RESULTADO OBTENIDEO: True (correcto)

    ¿POR QUÉ?: 'verifyA' sustituye los valores en las tres cláusulas:
    1. [LVar "p", Neg "q", LVar "r"] -> [True, False, True] -> Su disyunción es True.
    2. [Neg "p", LVar "q", LVar "r"] -> [False, True, True] -> Su disyunción es True.
    3. [LVar "q", LVar "r"]          -> [True, True]        -> Su disyunción es True.

    Como todas las cláusulas evaluaron a True, la conjunción es True.
-}

solucionInvalidaSAT :: SolA
solucionInvalidaSAT = [("p", True), ("q", False), ("r", False)]

pruebaVerifyFalseSAT :: Bool
pruebaVerifyFalseSAT = verifyA (ejemploSAT, solucionInvalidaSAT)

{-
    RESULTADO OBTENIDO: False (correcto)

    ¿POR QUÉ?: Al evaluar la tercera cláusula [LVar "q", LVar "r"] con estos valores,
    ambos literales se vuelven False: [False, False]. Por tanto la disyunción da False,
    esta cláusula colapsa a False, haciendo que por dominación (del and) toda la fórmula
    sea automáticamente False.
-}

pruebaSolveSAT :: SolA
pruebaSolveSAT = solveA ejemploSAT

{-
    RESULTADO OBTENIDO: [("p", True), ("q", True), ("r", True)] (correcto)

    ¿POR QUÉ?: Es la primera combinación generada por la tabla de verdad en la que
    verifyA (ejemploSAT, solucion) devuelve True.
-}

-- 2.1 Verificadores en χ (PROBLEMA A)
-- La complejidad algoritmica de los vrificadores en Chi
-- se encuentra detallada al final del archivo.

{- Chi

eq = rec eq.\m.\n.case m of {
    O -> [] case n of {
        O -> [] True [];
        S -> [x] False [];
    };
    S -> [x] case n of {
        O -> [] False [];
        S -> [y] eq x y;
    };
}

not = \b.
  case b of {
    True -> [] False [];
    False -> [] True [];
  }

or = rec or.\bs.
  case bs of {
    Nil -> [] False [];
    Cons -> [x, xs] case x of {
        True -> [] True [];
        False -> [] or xs;
      };
  }

all = rec all.\p.\bs.
  case bs of {
    Nil -> [] True [];
    Cons -> [x, xs] case p x of {
        True -> [] all p xs;
        False -> [] False [];
      };
  }

lookup = rec lookup.\x.\as.
  case as of {
    Nil -> [] Nothing;
    Cons -> [y, ys] case y of {
      Pair -> [x', v] case eq x x' of {
        True -> [] Just [v];
        False -> [] lookup x ys;
      };
    };
  }

mapJust = \f.\m.
  case m of {
    Just -> [j] Just [f j];
    Nothing -> [] Nothing;
  }

getVal = \sol.\lit.
  case lit of {
    Var -> [v] lookup v sol;
    Neg -> [v] mapJust not (lookup v sol);
  }

mapMaybe = rec mapMaybe.\f.\ls.
  case ls of {
    Nil -> [] Just [Nil []];
    Cons -> [x, xs] case f x of {
      Just -> [x'] case mapMaybe f xs of {
        Just -> [xs'] Just [Cons [x', xs']];
        Nothing -> [] Nothing [];
      };
      Nothing -> [] Nothing [];
    }
  }

substituteList = \sol.\ls.mapMaybe (getVal sol) ls

substitute = \dom.\sol.mapMaybe (substituteList sol) dom

verifyA = \dom.\sol.
  case substitute dom sol of {
    Just -> [ss] all or ss;
    Nothing -> [] False [];
  }

-}

-- Chi embebido en Haskell

{- ORMOLU_DISABLE -}
eqE :: Expr
eqE =
    Rec "eq" $ Lambda "m" $ Lambda "n" $ Case (Var "m") [
        ("O", ([], Case (Var "n") [
            ("O", ([], Cons "True" [])),
            ("S", (["x"], Cons "False" []))
            ])),
        ("S", (["x"], Case (Var "n") [
            ("O", ([], Cons "False" [])),
            ("S", (["y"], Var "eq" `Apl` Var "x" `Apl` Var "y"))
            ]))
    ]

notE :: Expr
notE =
    Lambda "b" $ Case (Var "b") [
        ("True", ([], Cons "False" [])),
        ("False", ([], Cons "True" []))
    ]

orE :: Expr
orE =
    Rec "or" $ Lambda "bs" $ Case (Var "bs") [
        ("Nil", ([], Cons "False" [])),
        ("Cons", (["x", "xs"], Case (Var "x") [
            ("True", ([], Cons "True" [])),
            ("False", ([], Var "or" `Apl` Var "xs"))
            ]))
    ]

allE :: Expr
allE =
    Rec "all" $ Lambda "p" $ Lambda "bs" $ Case (Var "bs") [
        ("Nil", ([], Cons "True" [])),
        ("Cons", (["x", "xs"], Case (Var "p" `Apl` Var "x") [
            ("True", ([], Var "all" `Apl` Var "p" `Apl` Var "xs")),
            ("False", ([], Cons "False" []))
            ]))
    ]

lookupE :: Expr
lookupE =
    Rec "lookup" $ Lambda "x" $ Lambda "as" $ Case (Var "as") [
        ("Nil", ([], Cons "Nothing" [])),
        ("Cons", (["y", "ys"], Case (Var "y") [
            ("Pair", (["x'", "v"], Case (eqE `Apl` Var "x" `Apl` Var "x'") [
                ("True", ([], Cons "Just" [Var "v"])),
                ("False", ([], Var "lookup" `Apl` Var "x" `Apl` Var "ys"))
                    ]))
            ]))
    ]

mapJustE :: Expr
mapJustE =
    Lambda "f" $ Lambda "m" $ Case (Var "m") [
        ("Just", (["j"], Cons "Just" [Var "f" `Apl` Var "j"])),
        ("Nothing", ([], Cons "Nothing" []))
    ]

getValE :: Expr
getValE =
    Lambda "sol" $ Lambda "lit" $ Case (Var "lit") [
        ("Var", (["v"], lookupE `Apl` Var "v" `Apl` Var "sol")),
        ("Neg", (["v"], mapJustE `Apl` notE `Apl` (lookupE `Apl` Var "v" `Apl` Var "sol")))
    ]

mapMaybeE :: Expr
mapMaybeE =
    Rec "mapMaybe" $ Lambda "f" $ Lambda "ls" $ Case (Var "ls") [
        ("Nil", ([], Cons "Just" [Cons "Nil" []])),
        ("Cons", (["x", "xs"], Case (Var "f" `Apl` Var "x") [
                ("Just", (["x'"], Case (Var "mapMaybe" `Apl` Var "f" `Apl` Var "xs") [
                        ("Just", (["xs'"], Cons "Just" [Cons "Cons" [Var "x'", Var "xs'"]])),
                        ("Nothing", ([], Cons "Nothing" []))
                    ])),
                ("Nothing", ([], Cons "Nothing" []))
            ]))
    ]

substituteListE :: Expr
substituteListE =
    Lambda "sol" $ Lambda "ls" $ mapMaybeE `Apl` (getValE `Apl` Var "sol") `Apl` Var "ls"

substituteE :: Expr
substituteE =
    Lambda "dom" $ Lambda "sol" $ mapMaybeE `Apl` (substituteListE `Apl` Var "sol") `Apl` Var "dom"

verifyAE :: Expr
verifyAE =
    Lambda "dom" $ Lambda "sol" $ Case (substituteE `Apl` Var "dom" `Apl` Var "sol") [
        ("Just", (["ss"], allE `Apl` orE `Apl` Var "ss")),
        ("Nothing", ([], Cons "False" []))
    ]
{- ORMOLU_ENABLE -}

-- 2.2 Ejemplos Chi (PROBLEMA A)

-- (p ∨ ¬q ∨ r) ∧ (¬p ∨ q ∨ r) ∧ (q ∨ r) | p = 1, q = 2, r = 3
ejemploChiSAT :: Expr
ejemploChiSAT =
  (k "Var" [natToChi 1] # k "Neg" [natToChi 2] # k "Var" [natToChi 3] # nil)
    # (k "Neg" [natToChi 1] # k "Var" [natToChi 2] # k "Var" [natToChi 3] # nil)
    # (k "Var" [natToChi 2] # k "Var" [natToChi 3] # nil)
    # nil

solucionChiValidaSAT :: Expr
solucionChiValidaSAT = k "Pair" [natToChi 1, true] # k "Pair" [natToChi 2, true] # k "Pair" [natToChi 3, true] # nil

pruebaChiVerifyTrueSAT :: Value
pruebaChiVerifyTrueSAT = eval $ verifyAE `Apl` ejemploChiSAT `Apl` solucionChiValidaSAT

{-
    RESULTADO OBTENIDEO: True (correcto)
-}

solucionChiInvalidaSAT :: Expr
solucionChiInvalidaSAT = k "Pair" [natToChi 1, true] # k "Pair" [natToChi 2, false] # k "Pair" [natToChi 3, false] # nil

pruebaChiVerifyFalseSAT :: Value
pruebaChiVerifyFalseSAT = eval $ verifyAE `Apl` ejemploChiSAT `Apl` solucionChiInvalidaSAT

{-
    RESULTADO OBTENIDO: False (correcto)
-}

-- 1.1 Representacion de dominios y soluciones (PROBLEMA B)

type V = Int

type E = (V, V)

type DomB = ([V], [E], E -> Double, [(V, V)], [(V, V)], Double)

type SolB = [V]

-- 1.2 Verificadores en tiempo polinomial (PROBLEMA B)

verifyB :: (DomB, SolB) -> Bool
verifyB ((vs, _, _, _, _, _), []) = null vs
verifyB ((vs, es, w, ps, xs, k), sol) =
  and
    [ coberturaTotal,
      consistenciaDeTransiciones,
      restriccionesDePrecedencia,
      exclusionesLocales,
      cotaDeCosto
    ]
  where
    -- Generamos los pares ordenados del ciclo (v_i, v_(i+1))
    adyacencias = zip sol (tail sol ++ [head sol])

    coberturaTotal = length vs == length sol && all (`elem` sol) vs

    consistenciaDeTransiciones = all (`elem` es) adyacencias

    restriccionesDePrecedencia =
      all
        ( \(u, v) ->
            ( do
                u_i <- u `elemIndex` sol
                v_i <- v `elemIndex` sol
                return $ u_i < v_i
            )
              `orElse` True
        )
        ps

    exclusionesLocales = all (`notElem` adyacencias) xs

    cotaDeCosto = sum (map w adyacencias) <= k

orElse :: Maybe a -> a -> a
orElse Nothing d = d
orElse (Just j) _ = j

{-
    JUSTIFICACIÓN DE ORDEN (verifyB):

    Sea n = |V| (longitud de la secuencia 'sol'), m = |E|, p = |P|, x = |X|.

    - adyacencias                   -> O(n)         (zip O(n) + (++) O(n) + tail O(1) + head O(1))
    - coberturaTotal                -> O(n^2)       (length O(n) + 'elem' por cada vs sobre sol: O(n*n))
    - consistenciaDeTransiciones    -> O(n * m)     ('elem' de cada adyacencia (n) sobre es (m))
    - restriccionesDePrecedencia    -> O(p * n)     (por cada par en P, elemIndex es O(n), dos veces)
    - exclusionesLocales            -> O(x * n)     (por cada exclusión, notElem sobre n adyacencias)
    - cotaDeCosto                   -> O(n)         (sum/map asumiendo w de costo O(1))

    Total: O(n^2 + n*m + p*n + x*n) = O( n * (n + m + p + x) )

    Como n, m, p y x son todos parte del tamaño de la entrada, esta cota es
    POLINOMIAL (cuadrática en el peor caso).
-}

-- 1.3 Resolucion en tiempo exponencial (PROBLEMA B)

solveB :: DomB -> SolB
solveB dom@(vs, _, _, _, _, _) =
  case find (\sol -> verifyB (dom, sol)) (permutations vs) of
    Just sol -> sol
    Nothing -> error "No solution"

{-
    JUSTIFICACIÓN DE ORDEN (solveB):

    Sea n = |V| (longitud de la secuencia 'sol'), m = |E|, p = |P|, x = |X|.

    'permutations vs' genera n! permutaciones, donde n = |V|.
    Para cada una, se evalúa verifyB, que es O(n(n+m+p+x)).

    Total: O( n! n * (n+m+p+x) )

    Es factorial en n.
-}

-- 1.4 Ejemplos Haskell (PROBLEMA B)

-- Grafo de 3 vértices (0,1,2) en triángulo, donde se exige pasar por 0 antes que por 1,
-- se prohíbe la transición directa (0,2) y el presupuesto máximo de costo es 4.0.
ejemploPlanificacion :: DomB
ejemploPlanificacion =
  ( [0, 1, 2],
    [(0, 1), (1, 2), (2, 0), (0, 2), (2, 1)],
    pesoArista,
    [(0, 1)],
    [(0, 2)],
    4.0
  )
  where
    pesoArista (0, 1) = 1.0
    pesoArista (1, 2) = 1.0
    pesoArista (2, 0) = 1.0
    pesoArista _ = 5.0

solucionValidaPlan :: SolB
solucionValidaPlan = [0, 1, 2]

pruebaVerifyTruePlan :: Bool
pruebaVerifyTruePlan = verifyB (ejemploPlanificacion, solucionValidaPlan)

{-
    RESULTADO OBTENIDO: True (correcto)

    ¿POR QUÉ?: 'verifyB' genera las adyacencias del ciclo: [(0,1), (1,2), (2,0)] y evalúa:
    1. Cobertura: Tiene todos los vértices sin repetir [0,1,2]. (True)
    2. Consistencia: Todas las adyacencias existen en el grafo. (True)
    3. Precedencia: El índice de 0 es menor que el de 1 (0 < 1). (True)
    4. Exclusiones: La arista prohibida (0,2) no forma parte del ciclo. (True)
    5. Costo: La suma de pesos es 1.0 + 1.0 + 1.0 = 3.0, que es menor o igual a 4.0. (True)

    Al cumplirse todas las condiciones concurrentes, el resultado es True.
-}

solucionInvalidaPlan :: SolB
solucionInvalidaPlan = [0, 2, 1]

pruebaVerifyFalsePlan :: Bool
pruebaVerifyFalsePlan = verifyB (ejemploPlanificacion, solucionInvalidaPlan)

{-
    RESULTADO OBTENIDO: False (correcto)

    ¿POR QUÉ?: El ciclo propuesto genera las adyacencias [(0,2), (2,1), (1,0)].
    Falla múltiples restricciones:
    1. Exclusiones: Contiene la arista prohibida (0,2).
    2. Costo: La arista (1,0) no está definida explícitamente en el costo económico,
       sumando un peso total que excede el límite de 4.0 (Dominación por cota de costo).
-}

pruebaSolvePlan :: SolB
pruebaSolvePlan = solveB ejemploPlanificacion

{-
    RESULTADO OBTENIDO: [0, 1, 2] (correcto)

    ¿POR QUÉ?: De todas las permutaciones posibles de los vértices, [0,1,2] es la primera
    que encuentra el algoritmo que satisface simultáneamente los criterios de orden,
    costo y demas restricciones validados por 'verifyB'.
-}

-- 2.1 Verificadores en χ (PROBLEMA B)
-- La complejidad algoritmica de los vrificadores en Chi
-- se encuentra detallada al final del archivo.

-- A las definiciones anteriores del bloque de Chi se le agregan las siguientes:

{- Chi

and = rec and.\ls.
  case ls of {
    Nil -> [] True [];
    Cons -> [x, xs] case x of {
            True -> [] and xs;
            False -> [] False [];
        };
  }

-- Extendemos eq para que permita pares
eq = rec eq.\m.\n.case m of {
    O -> [] case n of {
        O -> [] True [];
        S -> [x] False [];
    };
    S -> [x] case n of {
        O -> [] False [];
        S -> [y] eq x y;
    };
    Pair -> [a, b] case n of {
      Pair -> [a', b']
        and Cons [eq a a', Cons [eq b b', Nil []]];
    }
}

head = \ls.
  case ls of {
    Cons -> [x, xs] x;
  }

tail = \ls.
  case ls of {
    Cons -> [x, xs] xs;
  }

zip = rec zip.\as.\bs.
  case as of {
    Nil -> [] Nil [];
    Cons -> [x, xs] case bs of {
            Nil -> [] Nil;
            Cons -> [y, ys] Cons [Pair [x, y], zip xs ys];
        };
  }

length = rec length.\ls.
  case ls of {
    Nil -> [] O [];
    Cons -> [x, xs] S [length xs];
  }

elem = rec elem.\x.\ls.
  case ls of {
    Nil -> [] False [];
    Cons -> [x', xs] case eq x' x of {
            True -> [] True [];
            False -> [] elem x xs;
        };
  }

notElem = \x.\ls.not (elem x ls)

map = rec map.\f.\ls.
  case ls of {
    Nil -> [] Nil [];
    Cons -> [x, xs] Cons [f x, map f xs];
  }

add = rec add.\m.\n.
  case m of {
    O -> [] n;
    S -> [x] S [add x n];
  }

sum = rec sum.\ls.
  case ls of {
    Nil -> [] O [];
    Cons -> [x, xs] add x (sum xs);
  }

concat = rec concat.\as.\bs.
  case as of {
  	Nil -> [] bs;
  	Cons -> [x, xs] Cons [x, concat xs bs];
  }

adyacencias = \sol.zip sol (concat (tail sol) (Cons [head sol, Nil []]))

coberturaTotal = \vs.\sol.and Cons [eq (length vs) (length sol), Cons [all (\x.elem x sol) vs, Nil []]]

consistenciaDeTransiciones = \es.\adyacencias.all (\x.elem x es) adyacencias

lt = rec lt.\m.\n.
  case m of {
  	O -> [] case n of {
  			O -> [] False [];
  			S -> [y] True [];
  		};
  	S -> [x] case n of {
  			O -> [] False [];
  			S -> [y] lt x y;
  		};
  }

lte = \m.\n.or Cons [lt m n, Cons [eq m n, Nil []]]

elemIndex = rec elemIndex.\i.\x.\ls.
  case ls of {
    Nil -> [] Nothing;
    Cons -> [x', xs] case eq x x' of {
      True -> [] Just [i];
      False -> [] elemIndex (add i (S [O []])) x xs;
    }
  }

restriccionesDePrecedencia = \ps.\sol.
  all (
  	\p.case p of {
  		Pair -> [u, v]
  			case elemIndex (O []) u sol of {
  				Just -> [ui] case elemIndex (O []) v sol of {
  					Just -> [vi] lt ui vi;
  					Nothing -> [] True [];
  				};
  				Nothing -> [] True [];
  			};
  	}
  ) ps

exclusionesLocales = \xs.\adyacencias.all (\x.notElem x adyacencias) xs

cotaDeCosto = \w.\k.\adyacencias.lte (sum (map w adyacencias)) k

verifyB = \vs.\es.\w.\ps.\xs.\k.\sol.
  and (Cons [
    		coberturaTotal vs sol,
    	 Cons [
    		consistenciaDeTransiciones es (adyacencias sol),
    	 Cons [
    		restriccionesDePrecedencia ps sol,
    	 Cons [
    		exclusionesLocales xs (adyacencias sol),
    	 Cons [
    		cotaDeCosto w k (adyacencias sol),
    	 Nil []]]]]])

-}

{- ORMOLU_DISABLE -}
andE :: Expr
andE =
  Rec "and" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "True" [])),
    ("Cons", (["x", "xs"], Case (Var "x") [
      ("True", ([], Var "and" `Apl` Var "xs")),
      ("False", ([], Cons "False" []))
    ]))
  ]

eqExtE :: Expr
eqExtE =
  Rec "eq" $ Lambda "m" $ Lambda "n" $ Case (Var "m") [
    ("O", ([], Case (Var "n") [
      ("O", ([], Cons "True" [])),
      ("S", (["x"], Cons "False" []))
    ])),
    ("S", (["x"], Case (Var "n") [
      ("O", ([], Cons "False" [])),
      ("S", (["y"], Var "eq" `Apl` Var "x" `Apl` Var "y"))
    ])),
    ("Pair", (["a", "b"], Case (Var "n") [
      ("Pair", (["a'", "b'"], andE `Apl` Cons "Cons" [Var "eq" `Apl` Var "a" `Apl` Var "a'", Cons "Cons" [Var "eq" `Apl` Var "b" `Apl` Var "b'", Cons "Nil" []]]))
    ]))
  ]

headE :: Expr
headE =
  Lambda "ls" $ Case (Var "ls") [
    ("Cons", (["x", "xs"], Var "x"))
  ]

tailE :: Expr
tailE =
  Lambda "ls" $ Case (Var "ls") [
    ("Cons", (["x", "xs"], Var "xs"))
  ]

zipE :: Expr
zipE =
  Rec "zip" $ Lambda "as" $ Lambda "bs" $ Case (Var "as") [
    ("Nil", ([], Cons "Nil" [])),
    ("Cons", (["x", "xs"], Case (Var "bs") [
      ("Nil", ([], Cons "Nil" [])),
      ("Cons", (["y", "ys"], Cons "Cons" [Cons "Pair" [Var "x", Var "y"], Var "zip" `Apl` Var "xs" `Apl` Var "ys"]))
    ]))
  ]

lengthE :: Expr
lengthE =
  Rec "length" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "O" [])),
    ("Cons", (["x", "xs"], Cons "S" [Var "length" `Apl` Var "xs"]))
  ]

elemE :: Expr
elemE =
  Rec "elem" $ Lambda "x" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "False" [])),
    ("Cons", (["x'", "xs"], Case (eqExtE `Apl` Var "x'" `Apl` Var "x") [
      ("True", ([], Cons "True" [])),
      ("False", ([], Var "elem" `Apl` Var "x" `Apl` Var "xs"))
    ]))
  ]

notElemE :: Expr
notElemE = Lambda "x" $ Lambda "ls" $ notE `Apl` (elemE `Apl` Var "x" `Apl` Var "ls")

mapE :: Expr
mapE =
  Rec "map" $ Lambda "f" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "Nil" [])),
    ("Cons", (["x", "xs"], Cons "Cons" [Var "f" `Apl` Var "x", Var "map" `Apl` Var "f" `Apl` Var "xs"]))
  ]

addE :: Expr
addE =
  Rec "add" $ Lambda "m" $ Lambda "n" $ Case (Var "m") [
    ("O", ([], Var "n")),
    ("S", (["x"], Cons "S" [Var "add" `Apl` Var "x" `Apl` Var "n"]))
  ]

sumE :: Expr
sumE =
  Rec "sum" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "O" [])),
    ("Cons", (["x", "xs"], addE `Apl` Var "x" `Apl` (Var "sum" `Apl` Var "xs")))
  ]

concatE :: Expr
concatE =
  Rec "concat" $ Lambda "as" $ Lambda "bs" $ Case (Var "as") [
    ("Nil", ([], Var "bs")),
    ("Cons", (["x", "xs"], Cons "Cons" [Var "x", Var "concat" `Apl` Var "xs" `Apl` Var "bs"]))
  ]

adyacenciasE :: Expr
adyacenciasE =
  Lambda "sol" $ zipE `Apl` Var "sol" `Apl` (concatE `Apl` (tailE `Apl` Var "sol") `Apl` Cons "Cons" [headE `Apl` Var "sol", Cons "Nil" []])

coberturaTotalE :: Expr
coberturaTotalE =
  Lambda "vs" $ Lambda "sol" $ andE `Apl` Cons "Cons" [eqExtE `Apl` (lengthE `Apl` Var "vs") `Apl` (lengthE `Apl` Var "sol"), Cons "Cons" [allE `Apl` Lambda "x" (elemE `Apl` Var "x" `Apl` Var "sol") `Apl` Var "vs", Cons "Nil" []]]

consistenciaDeTransicionesE :: Expr
consistenciaDeTransicionesE =
  Lambda "es" $ Lambda "adyacencias" $ allE `Apl` Lambda "x" (elemE `Apl` Var "x" `Apl` Var "es") `Apl` Var "adyacencias"

ltE :: Expr
ltE =
  Rec "lt" $ Lambda "m" $ Lambda "n" $ Case (Var "m") [
    ("O", ([], Case (Var "n") [
      ("O", ([], Cons "False" [])),
      ("S", (["y"], Cons "True" []))
    ])),
    ("S", (["x"], Case (Var "n") [
      ("O", ([], Cons "False" [])),
      ("S", (["y"], Var "lt" `Apl` Var "x" `Apl` Var "y"))
    ]))
  ]

lteE :: Expr
lteE =
  Lambda "m" $ Lambda "n" $ orE `Apl` Cons "Cons" [ltE `Apl` Var "m" `Apl` Var "n", Cons "Cons" [eqE `Apl` Var "m" `Apl` Var "n", Cons "Nil" []]]

elemIndexE :: Expr
elemIndexE =
  Rec "elemIndex" $ Lambda "i" $ Lambda "x" $ Lambda "ls" $ Case (Var "ls") [
    ("Nil", ([], Cons "Nothing" [])),
    ("Cons", (["x'", "xs"], Case (eqExtE `Apl` Var "x" `Apl` Var "x'") [
      ("True", ([], Cons "Just" [Var "i"])),
      ("False", ([], Var "elemIndex" `Apl` (addE `Apl` Var "i" `Apl` Cons "S" [Cons "O" []]) `Apl` Var "x" `Apl` Var "xs"))
    ]))
  ]

restriccionesDePrecedenciaE :: Expr
restriccionesDePrecedenciaE =
  Lambda "ps" $ Lambda "sol" $ allE `Apl` Lambda "p" (Case (Var "p") [
    ("Pair", (["u", "v"], Case (elemIndexE `Apl` Cons "O" [] `Apl` Var "u" `Apl` Var "sol") [
      ("Just", (["ui"], Case (elemIndexE `Apl` Cons "O" [] `Apl` Var "v" `Apl` Var "sol") [
        ("Just", (["vi"], ltE `Apl` Var "ui" `Apl` Var "vi")),
        ("Nothing", ([], Cons "True" []))
      ])),
      ("Nothing", ([], Cons "True" []))
    ]))
  ]) `Apl` Var "ps"

exclusionesLocalesE :: Expr
exclusionesLocalesE =
  Lambda "xs" $ Lambda "adyacencias" $ allE `Apl` Lambda "x" (notElemE `Apl` Var "x" `Apl` Var "adyacencias") `Apl` Var "xs"

cotaDeCostoE :: Expr
cotaDeCostoE =
  Lambda "w" $ Lambda "k" $ Lambda "adyacencias" $ lteE `Apl` (sumE `Apl` (mapE `Apl` Var "w" `Apl` Var "adyacencias")) `Apl` Var "k"

verifyBE :: Expr
verifyBE =
  Lambda "vs" $ Lambda "es" $ Lambda "w" $ Lambda "ps" $ Lambda "xs" $ Lambda "k" $ Lambda "sol" $
  andE `Apl`
    Cons "Cons" [
      coberturaTotalE `Apl` Var "vs" `Apl` Var "sol",
    Cons "Cons" [
      consistenciaDeTransicionesE `Apl` Var "es" `Apl` (adyacenciasE `Apl` Var "sol"),
    Cons "Cons" [
      restriccionesDePrecedenciaE `Apl` Var "ps" `Apl` Var "sol",
    Cons "Cons" [
      exclusionesLocalesE `Apl` Var "xs" `Apl` (adyacenciasE `Apl` Var "sol"),
    Cons "Cons" [
      cotaDeCostoE `Apl` Var "w" `Apl` Var "k" `Apl` (adyacenciasE `Apl` Var "sol"),
    Cons "Nil" []]]]]]
{- ORMOLU_ENABLE -}

-- 2.2 Ejemplos Chi (PROBLEMA B)

-- Grafo de 3 vértices (0,1,2) en triángulo, donde se exige pasar por 0 antes que por 1,
-- se prohíbe la transición directa (0,2) y el presupuesto máximo de costo es 4.0.
ejemploChiPlanificacion :: (Expr, Expr, Expr, Expr, Expr, Expr)
ejemploChiPlanificacion =
  ( natToChi 0 # natToChi 1 # natToChi 2 # nil,
    p (natToChi 0, natToChi 1)
      # p (natToChi 1, natToChi 2)
      # p (natToChi 2, natToChi 0)
      # p (natToChi 0, natToChi 2)
      # p (natToChi 2, natToChi 1)
      # nil,
    pesoArista,
    p (natToChi 0, natToChi 1) # nil,
    p (natToChi 0, natToChi 2) # nil,
    natToChi 4
  )
  where
    pesoArista :: Expr
    pesoArista =
      Lambda "a" $
        Case
          ( orE
              `Apl` ( (eqExtE `Apl` Var "a" `Apl` p (natToChi 0, natToChi 1))
                        # (eqExtE `Apl` Var "a" `Apl` p (natToChi 1, natToChi 2))
                        # (eqExtE `Apl` Var "a" `Apl` p (natToChi 2, natToChi 0))
                        # nil
                    )
          )
          [ ("True", ([], natToChi 1)),
            ("False", ([], natToChi 5))
          ]

solucionChiValidaPlan :: Expr
solucionChiValidaPlan = natToChi 0 # natToChi 1 # natToChi 2 # nil

pruebaChiVerifyTruePlan :: Value
pruebaChiVerifyTruePlan = eval $ verifyBE `Apl` vs `Apl` es `Apl` w `Apl` ps `Apl` xs `Apl` k `Apl` solucionChiValidaPlan
  where
    (vs, es, w, ps, xs, k) = ejemploChiPlanificacion

{-
    RESULTADO OBTENIDO: True (correcto)
-}

solucionChiInvalidaPlan :: Expr
solucionChiInvalidaPlan = natToChi 0 # natToChi 2 # natToChi 1 # nil

pruebaChiVerifyFalsePlan :: Value
pruebaChiVerifyFalsePlan = eval $ verifyBE `Apl` vs `Apl` es `Apl` w `Apl` ps `Apl` xs `Apl` k `Apl` solucionChiInvalidaPlan
  where
    (vs, es, w, ps, xs, k) = ejemploChiPlanificacion

{-
    RESULTADO OBTENIDO: False (correcto)
-}

{- Ordenes en Chi
    JUSTIFICACIÓN DE ORDEN Y COMPARACIÓN (verifyAE, verifyBE):

    Estructuralmente, las funciones en χ (eq, or, all, lookup, mapMaybe, getVal,
    substitute, verifyA / and, elem, map, sum, lt, lte, elemIndex, verifyB)
    son traducciones directas de sus análogas en Haskell: misma cantidad de
    llamadas recursivas en función del tamaño de las listas de entrada. Por lo
    tanto, EN TÉRMINOS DE CANTIDAD DE PASOS DE REDUCCIÓN, verifyAE conserva el
    orden O(n*l*v) de verifyA, y verifyBE conserva el orden O(n*(n+m+p+x)) de
    verifyB: en ambos casos, POLINOMIAL en el tamaño de la entrada.

    Sin embargo hay una diferencia importante de costo, debido a la codificación
    de los datos en χ:

    - Las variables/vértices se codifican como naturales de Peano (natToChi),
    es decir en UNARIO (O, S, S, S, ...). La función 'eq' (y por extensión
    'lt', 'lte', 'add') compara/recorre estos naturales recursivamente, con
    costo O(valor) en lugar de O(1), como sí lo sería comparar un Int o un
    String corto en Haskell (donde 'lookup'/'==' tienen costo prácticamente
    constante para identificadores chicos).

    - Esto agrega un factor multiplicativo extra, dependiente de la magnitud
    de los identificadores usados (no solo de la cantidad de elementos):

        verifyAE: O(n * l * v * Vmax)
        verifyBE: O(n * (n+m+p+x) * Vmax)

    donde Vmax es el mayor valor numérico usado para identificar una
    variable o vértice.

    CONCLUSIÓN: ambos verificadores siguen siendo polinomiales en el tamaño
    (unario) de la entrada, igual que sus versiones en Haskell, pero con una
    constante/factor adicional producto de la representación unaria de los
    naturales en χ. Esto no cambia la clase de complejidad (P), pero sí hace
    que, para identificadores grandes, χ sea notoriamente más lento en
    la práctica que el equivalente en Haskell (que usa representación binaria
    nativa de Int).
-}
