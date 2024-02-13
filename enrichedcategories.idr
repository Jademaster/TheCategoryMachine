
import Data.Fin
import Data.List

data TwoOps x a = Val x | Addunit | Mulunit | Add a a | Mul a a

Algebra : (Type -> Type) -> Type -> Type  
Algebra f a = f a -> a

nats : Algebra (TwoOps Nat) Nat
nats (Val x) = x
nats (Addunit) = 0
nats (Mulunit) = 1
nats ((Add x y)) = x + y
nats ((Mul x y)) = x * y

Trop : Algebra (TwoOps (Maybe Double)) (Maybe Double)
Trop (Val x) = x
Trop Addunit = Nothing
Trop Mulunit = Just 0
Trop (Add Nothing y) = y 
Trop (Add x Nothing) = x 
Trop (Add (Just x) (Just y)) = Just (min x y)
Trop (Mul Nothing y) = Nothing 
Trop (Mul x Nothing) = Nothing 
Trop (Mul (Just x) (Just y)) = Just (x + y)

Graph : Type -> Type
Graph r = r -> r -> Type

EGraph : Nat -> Type -> Type
EGraph n r =  Fin n -> Fin n -> r 

sumVect : {n : Nat} -> (a -> a -> a) -> a -> (Fin n -> a) -> a
sumVect {n=Z} f z v = z
sumVect {n=S i} f z v = f (v FZ) (sumVect {n=i} f z (v . FS))


compose : (a -> a -> TwoOps a a) -> (TwoOps a a -> a) -> a -> a -> a 
compose f1 f2 = \a1, a2 => f2 (f1 a1 a2)

Addalg : Algebra (TwoOps a) a -> (a -> a -> a)
Addalg = compose Add

AlgMat : {a : Type} -> {n : Nat} ->  Algebra (TwoOps a) a -> Algebra (TwoOps (EGraph n a)) (EGraph n a)
AlgMat alg (Val m) = m
AlgMat alg (Addunit) = \i, j => (alg Addunit)
AlgMat alg (Mulunit) = \i, j => if i == j then (alg Addunit) else (alg Mulunit)
AlgMat alg (Add m1 m2) = \i, j => alg (Add (m1 i j) (m2 i j))
AlgMat alg (Mul m1 m2) = \i, j => sumVect {n} (Addalg alg) (alg Addunit) (\k => (alg (Mul (m1 i k) (m2 k j))))

-- example
G : EGraph 2 Nat
G FZ FZ = 3
G FZ (FS FZ) = 2
G (FS FZ) FZ = 4
G (FS FZ) (FS FZ)=3

H : EGraph 2 Nat
H= AlgMat nats (Mul G G)

--streams 
Index : Nat -> Stream a -> a 
Index Z (x :: xs) = x
Index (S i) (x :: xs) = Index i xs

Mulbyg : {o : Nat} -> {r : Type} -> (Algebra (TwoOps r) r) -> EGraph o r -> Stream (EGraph o r) -> Stream (EGraph o r)
Mulbyg alg g (x :: xs) =  ((AlgMat alg) (Mul g x)) :: (Mulbyg alg g xs)

FreeECat : {o: Nat} -> {r: Type} -> Algebra (TwoOps r) r -> EGraph o r -> Stream (EGraph o r)
FreeECat alg g = ((AlgMat alg) Mulunit) :: Mulbyg alg g (FreeECat alg g)

EGraphMor : (obj, obj' : Nat) -> (r : Type) -> (v : Graph r) -> EGraph obj r -> EGraph obj' r -> (f: (Fin obj) -> (Fin obj'))-> Type 
EGraphMor obj obj' r v g h f=  (s,t : Fin obj) ->  v (g s t) (h (f s) (f t)) 

Enrichedcat : (o : Nat) ->(r : Type) -> Nat -> (v : Graph r) -> (alg : Algebra (TwoOps r) r) -> (g : EGraph o r) -> Type
Enrichedcat o r n v alg g = EGraphMor o o r v (Index n (FreeECat alg g)) g id

--languages
Languages : Type
Languages = List (List Char)

Mulbyword : List Char -> Languages -> Languages
Mulbyword w Nil = Nil
Mulbyword w (x :: xs) = (w ++ x) :: (Mulbyword w xs) 

LanguageSemiring : Algebra (TwoOps Languages) Languages
LanguageSemiring (Val l) = l
LanguageSemiring (Addunit) = Nil
LanguageSemiring (Mulunit) = [Nil]
LanguageSemiring (Add l1 l2) = union l1 l2 
LanguageSemiring (Mul l1 l2) = concat l1 l2 where
    concat : Languages -> Languages -> Languages 
    concat Nil y = Nil
    concat (x :: xs) ys = union (Mulbyword x ys) (concat xs ys)

Machine : EGraph 2 Languages
Machine FZ FZ = Nil
Machine (FS FZ) (FS FZ) = Nil
Machine (FZ) (FS FZ) = ['a'] :: Nil
Machine (FS FZ) FZ =  ['b'] :: Nil

Alternatingwords : Stream (EGraph 2 Languages)
Alternatingwords = FreeECat LanguageSemiring Machine


