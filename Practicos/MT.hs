module MT where

import Data.Maybe
import Prelude (Eq, String, lookup, return, undefined, ($))

-- Componentes

data Q
  = Init
  | Halt
  | Q String
  deriving (Eq)

type Symbol = String

type Tape = ([Symbol], Symbol, [Symbol])

blank :: Symbol
blank = "#"

wildcard :: Symbol
wildcard = "_"

-- Control

data Action
  = Left
  | Right
  | Write Symbol

type Branch = (Symbol, (Action, Q))

type M = [(Q, [Branch])]

-- Semantica

exec :: Tape -> M -> Tape
exec t m = t'
  where
    (t', Halt) = iter t m Init

iter :: Tape -> M -> Q -> (Tape, Q)
iter t m Halt = (t, Halt)
iter t m q = iter t' m q'
  where
    (t', q') = step t (fromJust $ lookup q m)

step :: Tape -> [Branch] -> (Tape, Q)
step t@(l, s, r) bs =
  case a of
    Left -> (left t, q')
    Right -> (right t, q')
    Write s' -> (write t s', q')
  where
    (a, q') = lookupActionState s bs

left :: Tape -> Tape
left ([], sym, right) = ([], blank, sym : right)
left (sym' : left, sym, right) = (left, sym', sym : right)

right :: Tape -> Tape
right (left, sym, []) = (sym : left, blank, [])
right (left, sym, sym' : right) = (sym : left, sym', right)

write :: Tape -> Symbol -> Tape
write (left, _, right) sym = (left, sym, right)

lookupActionState :: Symbol -> [Branch] -> (Action, Q)
lookupActionState s bs =
  case lookup s bs of
    Just b -> b
    Nothing -> fromJust $ lookup wildcard bs

mL :: Symbol -> M
mL s =
  [ ( Init,
      [ (wildcard, (Left, Init)),
        (s, (Write s, Halt))
      ]
    )
  ]
