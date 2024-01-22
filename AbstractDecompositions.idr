-- graphs and decompositions
import SemiringsAndMatrices

Graph : (obj : Type) -> Type
Graph a = a -> a -> Type

GraphMor : {obj, obj' : Type} -> (f : obj -> obj') -> Graph obj -> Graph obj' -> Type 
GraphMor {obj, obj'} f g h = {s, t : obj} -> g s t -> h (f s) (f t)

-- free category
data Path : {obj : Type} -> Graph obj -> Graph obj where 
  Id : Path g a a 
  Comp : {g : Graph obj} -> g a b -> Path g b c -> Path g a c
  

bool : Graph Bool
bool True False = Fin 0
bool False True = Fin 1
bool False False = Fin 1
bool True True = Fin 1

Types : Graph Type
Types a b = a -> b

Fintypes : Graph Fintype
Fintypes (MkDPair n n1) (MkDPair m m1) = (Fin n -> Fin m)

rmats : (r : Type) -> Graph Nat
rmats r n m = Matrix n m r



-- the two change of base functions we need

Freetype : Bool -> Type
Freetype True = Fin 1
Freetype False = Void

Freer : (r : Type) -> Algebra (TwoOps r) r -> Bool -> r
Freer r alg True = alg (Mulunit)
Freer r alg False = alg (Addunit)
    
EGraph : Type -> Type -> Type
EGraph o r = o -> o -> r 



--a graph enriched in set is an ordinary graph
IdrGraph : (obj : Type) -> Type
IdrGraph o = EGraph o Type

EGraphMor : (obj, obj', r : Type) -> (v : Graph r) -> EGraph obj r -> EGraph obj' r -> (f: obj -> obj')-> Type 
EGraphMor obj obj' r v g h f=  (s,t : obj) ->  v (g s t) (h (f s) (f t)) 

CBase : (verts, obj, obj' : Type) -> (f : obj -> obj') -> EGraph verts obj -> EGraph verts obj' 
CBase verts obj obj' f g  = (\i, j =>  f (g i j))

--Depgraph : (verts, r : Type) -> (f : verts -> Fintype) -> (shape : EGraph verts Bool) -> Type
--Depgraph verts r f shape = EGraphMor verts Fintype Type (types) (CBase verts Bool Type Freetype shape) (rmats r) f
{-- 
Depgraph' : (verts, r : type) -> (f : verts-> Type) -> (shape : EGraph verts Bool) -> Type
Depgraph' verts r f = (s,t : verts) -> (CBase shape freetype) s t -> (f s -> f t -> r)
--}
Depgraph'' : (verts : Nat) -> (r : Type) -> (f : Fin verts-> Nat) -> (shape : Matrix verts verts Bool) -> Type
Depgraph'' verts r f shape = (s, t : (Fin verts)) -> Matrix (f s) (f t) r

--example

-- example shape

Sh : Matrix 2 2 Bool
Sh Zero Zero = True
Sh (Suc Zero) (Suc Zero) = True
Sh Zero (Suc Zero) = True
Sh (Suc Zero) Zero = True
Sh _ _ = False




 -- object component
 
{--
Fob : Fin 2 -> Fintype 
Fob Zero = MkDPair 20 (Zero)
Fob (Suc Zero) = MkDPair 81 (Suc (Zero))
--}
Fob : Fin 2 -> Nat
Fob Zero = 20
Fob (Suc Zero) = 81


--each edge is mapped to a matrix valued in the tropical semiring
d : Depgraph'' (2) (Maybe Double) Fob Sh
d = fmor where
    fmor : (a, b : (Fin 2)) -> rmats (Maybe Double) (Fob a) (Fob b)
    fmor Zero Zero = (\i, j => if i==j then Just 0 else Just 3.8)
    fmor Zero (Suc Zero) = (\i, j => Nothing)--if (i==j) then (Just 2.4) else Nothing)
    fmor (Suc Zero) Zero = (\i, j => Nothing)-- if (i==j) then (Just 23) else Nothing)
    fmor (Suc Zero) (Suc Zero) = (\i, j => if i==j then Just 0 else Just 9.9)


Adddepgraph : (verts : Nat) -> (s : Type) -> (fob : Fin verts -> Nat) -> (alg : Algebra (TwoOps Bool) Bool) -> (salg : Algebra (TwoOps s) s) -> (sh, sh' : Matrix verts verts Bool) -> Depgraph'' (verts) s fob sh -> Depgraph'' (verts) s fob sh' -> Depgraph'' (verts) s fob (AlgMat {a=Bool} {n=verts} alg (Add sh sh'))-- left here with Zanzi Nov. 3rd.
Adddepgraph n s fob alg salg sh sh' d d' = \i, j => (\a, b => salg( Add (d i j a b) (d' i j a b)))

-- example sum
Sum : Depgraph'' (2) (Maybe Double) Fob Sh
Sum = Adddepgraph 2 (Maybe Double) (Fob) (Bools) (Trop) Sh Sh d d


--algebra transformer to dependent graphs
--Algdecomp : (r, verts : Type) -> (f : verts -> Type) -> (shape : Egraph verts Bool) Algebra (TwoOps r) r -> Algebra (TwoOps (Depgraph verts r f shape)) (Depgraph verts r f shape)
--Algdecomp r verts f shape alg (Val d)= d
--identity decomposition has zero matrices everywhere
--Algdecomp r verts f shape alg (Addunit)= (\a, b => (\i, j => alg Addunit))
--Algdecomp r verts f shape alg (Mulunit)= (\a, b => if a==b then (\i, j => if (i==j) alg Mulunit else alg Addunit) else (\i, j => Addunit))

--Fibgraph : (verts, r : Type) -> (v : Graph r) -> (alg : Algebra (TwoOps r) r) -> (shape : EGraph verts Bool) -> Type
--Fibgraph verts r v alg shape = (a : Type) -> (tot : EGraph a r) -> EGraphMor a verts r v tot (CBase verts Bool r (Freer r alg) shape)

--RGroth : (verts, r : Type) -> (v : Graph r) -> (alg : Algebra (TwoOps r) r) -> (shape : EGraph verts Bool) -> Depgraph verts r shape -> Fibgraph verts r v alg shape
--RGroth verts r v alg shape decomp = DPair (Fin 2) (fst decomp)



