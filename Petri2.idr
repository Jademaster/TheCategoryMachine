import Data.Fin

Petrinet : Nat -> Type
Petrinet places  = (s : (Fin places) -> Nat) ->(t:(Fin  places) -> Nat) -> Type

--example
Net : Petrinet 2 
Net f1 f2 = if (f1 FZ == 1) && (f1 (FS FZ) == 1) && (f2 FZ == 2) && (f2 (FS FZ) == 0) then Fin 1 else Fin 0

fplus : (x -> Nat) -> (x -> Nat) -> (x -> Nat)
fplus f g = \i => f i +  g i

data Freecmc : (Petrinet n) -> (Fin n -> Nat) -> (Fin n -> Nat) -> Type where
    Id : (net : Petrinet n) -> (s : Fin n -> Nat) ->Freecmc net s s
    Gen : (net : Petrinet n) -> (s,t : Fin n -> Nat) -> (net s t) -> Freecmc net s t
    Comp : (net : Petrinet n) -> (s, t, r : Fin n -> Nat) -> (Freecmc net s t) -> (Freecmc net t r) -> (Freecmc net s r)
    Par : (net : Petrinet n) -> (s, s', t, t' : Fin n -> Nat) -> Freecmc net s t -> Freecmc net s' t' -> Freecmc net (fplus s s') (fplus t t')

A : Fin 2 -> Nat
A FZ = 1
A (FS FZ) = 1

B : Fin 2 -> Nat
B FZ = 2
B (FS FZ) = 0

term : Freecmc Net A B
term = Comp Net A A B (Id Net A) (Gen Net A B FZ)

--Colored Petrinets

Alg : Petrinet n-> Petrinet m -> Type
Alg p q = DPair  (Fin n -> Fin m) (\f => ({x, y : (Fin n -> Nat)} -> p x y -> q (f x) (f y)))


    
    
