import Data.Fin
import Data.Vect

Petrinet : Nat -> Type
Petrinet places  = (Vect places Nat) ->(Vect places Nat) -> Type

-- a Petri net with a single transition a + b -> 2 a
Net : Petrinet 2
Net (m1 :: m2 :: Nil) (n1 :: n2 :: Nil) = if m1 == 1 && m2 == 1 && n1 == 2 && n2 == 0 then (Fin 1) else (Fin 0)

