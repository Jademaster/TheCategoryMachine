-- this file implements the Grothendieck construction and its inverse for functions i.e.\ the equivalence between functions f : X -> Set and functions \int f -> X. In the language of functional programming, this gives a reversible procedure for turning dependent types into function types.

-- finite sets with n elements

  
-- just a dependent type
import Data.Vect

Deptype :Type -> Type
Deptype x = x -> Type

-- example 1: the dependent type sending a natural number n to the type Fin n

F: Deptype Nat
F = Fin

-- example 2: 

G : (a : Type) -> Deptype Nat
G a = (\n => Vect n a)

-- these dependent types have corresponding function types

f : (DPair Nat Fin) -> Nat
f = fst

g : (DPair Nat G) -> Nat
g = fst

-- this is beccause function types are just another side to dependent types

functype: Type -> Type -> Type
functype x y = y -> x

-- to turn a dependent type into a function type

Groth : {x : Type} -> Deptype x -> (DPair Type (functype x))
Groth {x} d = MkDPair (DPair x d) fst

-- and inverting a function type into a dependent type

Inv : {x : Type} -> {y : Type} -> functype x y -> Deptype x
Inv {x} {y} f = finv where
  finv : x -> Type
  finv a = DPair y (\b => (f b = a))
  
-- should do the 1-dimensional version: between functors F : C -> Cat and functors \int F -> C
  

  

  

  
  


  

