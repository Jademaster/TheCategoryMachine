import Data.Fin
import Data.List
import Data.Singleton
import Data.List.Quantifiers

data TwoOps x a = Val x | Addunit | Mulunit | Add a a | Mul a a

Algebra : (Type -> Type) -> Type -> Type  
Algebra f a = f a -> a
 
nats : Algebra (TwoOps Nat) Nat
nats (Val x) = x
nats (Addunit) = 0
nats (Mulunit) = 1
nats ((Add x y)) = x + y
nats ((Mul x y)) = x * y

Semiring : Type -> Type
Semiring a = Algebra (TwoOps a) a

Trop : Semiring (Maybe Double)
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
Graph obj = obj -> obj -> Type
 
EGraph : Nat -> Type -> Type
EGraph n r =  Fin n -> Fin n -> r 

EMat : Nat -> Nat -> Type -> Type
EMat rows cols r =  Fin rows -> Fin cols -> r

sumVect : {n : Nat} -> (a -> a -> a) -> a -> (Fin n -> a) -> a
sumVect {n=Z} f z v = z
sumVect {n=S i} f z v = f (v FZ) (sumVect {n=i} f z (v . FS))

AlgMat : {a : Type} -> {n : Nat} ->  Semiring a -> Semiring (EGraph n a)
AlgMat alg (Val m) = m
AlgMat alg (Addunit) = \i, j => (alg Addunit)
AlgMat alg (Mulunit) = \i, j => if i == j then (alg Addunit) else (alg Mulunit)
AlgMat alg (Add m1 m2) = \i, j => alg (Add (m1 i j) (m2 i j))
AlgMat alg (Mul m1 m2) = \i, j => sumVect {n} (curry (alg . uncurry (Add))) (alg Addunit) (\k => (alg (Mul (m1 i k) (m2 k j))))

 -- mixed dimension matrix multiplication
MatMul : {m, n, o : Nat} -> {r : Type} -> {alg : Semiring r} -> EMat m n r -> EMat n o r -> EMat m o r
MatMul a b = (\i, j => sumVect {n} (curry (alg . uncurry (Add))) (alg Addunit) (\k => (alg (Mul (a i k) (b k j)))))

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

Mulbyg : {o : Nat} -> {r : Type} -> (Semiring r) -> EGraph o r -> Stream (EGraph o r) -> Stream (EGraph o r)
Mulbyg alg g (x :: xs) =  ((AlgMat alg) (Mul g x)) :: (Mulbyg alg g xs)

FreeECat : {o: Nat} -> {r: Type} -> Semiring r -> EGraph o r -> Stream (EGraph o r)
FreeECat alg g = ((AlgMat alg) Mulunit) :: Mulbyg alg g (FreeECat alg g)

EGraphMor : (obj, obj' : Nat) -> (r : Type) -> (v : Graph r) -> EGraph obj r -> EGraph obj' r -> (f: (Fin obj) -> (Fin obj'))-> Type 
EGraphMor obj obj' r v g h f=  (s,t : Fin obj) ->  v (g s t) (h (f s) (f t)) 

Enrichedcat : (o : Nat) ->(r : Type) -> Nat -> (v : Graph r) -> (alg : Semiring r) -> (g : EGraph o r) -> Type
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

main : IO ()
main = print ((Index 6 Alternatingwords) FZ (FS FZ))

-- let's index

--large graph to large graph morphisms
record GraphMor where
    constructor MkGraphMor
    obj : Type
    obj' : Type
    g : Graph obj
    h : Graph obj'
    f : obj -> obj'
    mor : (s,t : obj) ->  ((g s t) -> (h (f s) (f t)))

-- it's "just" a graph morphism from a language enriched graph to Rmat.

record IEgraph where
    constructor MkIEgraph
    obj : Nat
    r : Type
    shape : EGraph obj Languages
    grouping : (Fin obj) -> Nat
    mor : (s,t : (Fin obj)) ->  Any Singleton (shape s t) ->  EMat (grouping s) (grouping t) r

-- an example

{-
Machine : EGraph 2 Languages
Machine FZ FZ = Nil
Machine (FS FZ) (FS FZ) = Nil
Machine (FZ) (FS FZ) = ['a'] :: Nil
Machine (FS FZ) FZ =  ['b'] :: Nil
 -}

fibers : Fin 2 -> Nat
fibers FZ = 20
fibers (FS  FZ) = 81

 -- helper function 
ToNat : {n : Nat} -> (Fin n) -> Nat
ToNat FZ = 0
ToNat (FS i) = (ToNat i) + 1


MyList : List (Char)
MyList = ['a','b']

f :Nat -> Any Singleton MyList
f n = There (Here (Singleton.Val 'b'))

toVect : {l : List (List Char)} -> (Any Singleton l ->  a) -> (Fin (length l) -> a)
toVect f = ?x

D : IEgraph 
D = MkIEgraph 2 Languages Machine fibers mapping where
    mapping : (a, b : (Fin 2)) -> Any Singleton (Machine a b) -> EMat (fibers a) (fibers b) Languages
    mapping FZ (FS FZ) (Here (Singleton.Val ['a'])) = (\i, j => if (ToNat i)==(ToNat j) then Nil else [['x']])
    mapping (FS  FZ) FZ (Here (Singleton.Val ['b'])) = (\i, j => if (ToNat i)== (ToNat j) then [['z']] else Nil)
    mapping _ _ _  = (\i, j => Nil)

ThickEGraph : Type -> Type -> Type
ThickEGraph obj r = obj -> obj -> r 

Groth : (d : IEgraph) -> (alg : Semiring d.r) -> ThickEGraph (DPair (Fin d.obj) (Fin . d.grouping)) d.r
Groth d alg = h where
    h : (DPair (Fin d.obj) (Fin . d.grouping)) -> (DPair (Fin d.obj) (Fin . d.grouping)) -> d.r
    h (MkDPair x a) (MkDPair y b) = sumVect (curry (alg . (uncurry Add))) (alg Addunit) (toVect (\f => d.mor x y f a b)) 

--Total : ThickEGraph (DPair (Fin 2) (Fin . D.grouping)) Languages
Total = Groth D LanguageSemiring

M : EMat 50 50 Languages
M = (\i, j => if (ToNat i) == (ToNat j) then [Nil] else Nil)
-- compositional language generation
FreeIECat : (d : IEgraph) -> (alg : Semiring d.r) -> Stream (IEgraph)
FreeIECat d alg = head :: Mulbyd d (FreeIECat alg d) where
    head : IEgraph
    head = MkIEgraph d.obj d.r idgraph d.grouping mor where
        idgraph : EGraph d.obj Languages
        idgraph = ((AlgMat LanguageSemiring) Mulunit)
        mor : (a, b : (Fin d.obj)) -> Any Singleton (idgraph a b) ->  EMat (d.grouping a) (d.grouping b) d.r
        mor a b (f) = ?q--((AlgMat LanguageSemiring) Mulunit)

    Mulbyd : IEgraph -> Stream (IEgraph) -> Stream (IEgraph)
    Mulbyd d (head :: tail) = MkIEgraph d.obj d.r (anotherStep) d.grouping mor :: Mulbyd d tail where
        anotherStep : EGraph d.obj Languages 
        anotherStep = ?k --(AlgMat LanguageSemiring) (Mul d.shape head.shape)

        mor : (a, b : (Fin d.obj)) -> Any Singleton (anotherStep a b) ->  EMat (d.grouping a) (d.grouping b) d.r
        mor a b (Here (Singleton.Val Nil)) = (\i,j => if (ToNat i)==(ToNat j) then [Nil] else Nil)
        mor a b (Here (Singleton.Val x::xs)) = MatMul (d.mor a b (Here (Singleton.Val x))) (mor a b (Here (Singleton.Val xs))) 
        mor a b (There x) = mor a b x


-- it's the singletons i don't understand...
        