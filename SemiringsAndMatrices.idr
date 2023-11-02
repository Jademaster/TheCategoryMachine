
export
data Mu : (pattern : Type -> Type) -> Type where
    In : {f: Type -> Type} -> f (Mu f) -> Mu f
    

export
data TwoOps x a = Val x | Addunit | Mulunit | Add a a | Mul a a

export
Functor (TwoOps x) where
  map f (Val y) = Val y
  map f (Addunit) = Addunit
  map f (Mulunit) = Mulunit
  map f (Add a1 a2) = Add (f a1) (f a2)
  map f (Mul a1 a2) = Mul (f a1) (f a2)

export
Freesemiring : Type -> Type
Freesemiring x = Mu (TwoOps x)

export
Algebra : (Type -> Type) -> Type -> Type  
Algebra f a = f a -> a

 --universal property of the initial algebra
export
cata : Functor f => Algebra f a -> Mu f -> a
cata alg (In op) = alg (map (cata alg) op)

export
nats : Algebra (TwoOps Nat) Nat
nats (Val x) = x
nats (Addunit) = 0
nats (Mulunit) = 1
nats ((Add x y)) = x + y
nats ((Mul x y)) = x * y


cata' : Algebra (TwoOps a) a -> Algebra Freesemiring a 
cata' = cata

-- use the universal property to freely extend nats

freenats = cata' nats

--min plus semiring

export
trop : Algebra (TwoOps (Maybe Double)) (Maybe Double)
trop (Val x) = x
trop Addunit = Nothing
trop Mulunit = Just 0
trop (Add Nothing y) = y 
trop (Add x Nothing) = x 
trop (Add (Just x) (Just y)) = Just (min x y)
trop (Mul Nothing y) = Nothing 
trop (Mul x Nothing) = Nothing 
trop (Mul (Just x) (Just y)) = Just (x + y)

-- the free extension

freetrop = cata' trop

export
data Fin : Nat -> Type where
  Zero : Fin (S n)
  Suc : (i : Fin n) -> Fin (S n)


export
Fintype : Type
Fintype = DPair Nat Fin

export
Size : Fintype -> Nat
Size (MkDPair n a) = n


export
Eq (Fin n) where
  Zero == Zero = True
  Suc (x) == Suc (y) = x == y
  Zero == Suc (y) = False
  Suc (x) == Zero = False
  x /= y = not (x == y)

-- the 2-rig of types

export
Tworig : Algebra (TwoOps Type) Type
Tworig (Val a) = a
Tworig Addunit = Void
Tworig Mulunit = Unit
Tworig (Add a b) = Either a b
Tworig (Mul a b) = (a,b)

-- boolean semiring
--bools : Algebra (TwoOps Bool) Bool
--bools Val a = a
--bools (Add a b) = a or b
--bools (Mul a b) = a and b
--bools (Addunit) = False
--bools (Mulunit) = True

--and its free extension

freetypes= cata' Tworig

--example
term : Freesemiring Type
term = In $ Mul (In (Val (Fin 4))) (In Addunit)
-- bigtype = freetypes term
-- did i just write a types compiler?

--Matrices

export
Matrix : Nat -> Nat -> Type -> Type
Matrix m n s = Fin m -> Fin n -> s

A : Matrix 2 2 Nat
A Zero Zero = 3
A Zero (Suc Zero) = 2
A (Suc Zero) Zero = 4
A (Suc Zero) (Suc Zero)=3


compose : (a -> a -> TwoOps a a) -> (TwoOps a a -> a) -> a -> a -> a 
compose f1 f2 = \a1, a2 => f2 (f1 a1 a2)


addalg : Algebra (TwoOps a) a -> (a -> a -> a)
addalg = compose Add


sumVect : {n : Nat} -> (a -> a -> a) -> a -> (Fin n -> a) -> a
sumVect {n=Z} f z v = z
sumVect {n=S i} f z v = f (v Zero) (sumVect {n=i} f z (v . Suc))

-- algebra transformer from semirings to matrices

export
AlgMat : {n : Nat} ->  Algebra (TwoOps a) a -> Algebra (TwoOps (Matrix n n a)) (Matrix n n a)
AlgMat alg (Val m) = m
AlgMat alg (Addunit) = \i, j => (alg Addunit)
AlgMat alg (Mulunit) = \i, j => if i == j then (alg Addunit) else (alg Mulunit)
AlgMat alg (Add m1 m2) = \i, j => alg (Add (m1 i j) (m2 i j))
AlgMat alg ((Mul m1 m2)) = \i, j => sumVect {n} (addalg alg) (alg Addunit) (\k => (alg (Mul (m1 i k) (m2 k j))))

-- example
Matsemiring = AlgMat nats
B : Matrix 2 2 Nat
B= Matsemiring (Mul A A)
