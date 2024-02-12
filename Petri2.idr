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
--Multifunction : List Type -> List Type -> Type
--Multifunction i o = (map ( , ) i ) -> (map ( , ) o)
--Alg : Petrinet n -> (Fin n -> Type) -> Type
--Alg net color = {s, t : Fin n -> Nat} -> (net s t) -> DPair (DPair (Fin . s) color)
    
    
Obd : Type -> Type
Obd s = s -> Type

Arc : {s: Type} -> {t : Type} -> (s -> t) -> Obd s -> Obd t -> Type
Arc f fam1 fam2 = {x : s} -> fam1 x -> fam2 (f x)

Families : Type
Families = DPair Type (\t => (t -> Type)) 

Familyfib : Families -> Type
Familyfib (MkDPair t fam) = t

--Obf : (Type -> Type) -> Type -> Type
--Obf f y = DPair Type (\x => (f x = y))
--Arcf : (f : Type -> Type) -> Functor f => (s, t : Type) -> ( s -> t) -> Obf f s -> Obf f t -> Type 
--Arcf h f s t (MkDPair a Refl) (MkDPair b Refl) = DPair (a -> b) (\k => (map k = h))

Obf : (Type -> Type) -> Type -> Type
Obf f y = DPair Type (\x => (f x = y))

Arcf : (func : Functor f) => (f : Type -> Type) -> (s, t : Type) -> (s -> t) -> Obf f s -> Obf f t -> Type
Arcf f s t h (MkDPair a p) (MkDPair b q) = DPair (a -> b) (\k => map @{func} k ~=~ h)

Preimage : (Type -> Type) -> Type -> Type
Preimage f y = DPair Type (\x => (f x ~=~ y))