import SemiringsAndMatrices
import Data.List

EGraph : Type -> Type -> Type
EGraph o r = o -> o -> r 

Ex : EGraph (Fin 2) (Maybe Double)
Ex Zero Zero = Just 0.5
Ex (Suc Zero) (Suc Zero) = Just 9.5
Ex Zero (Suc Zero) = Just 1.0
Ex (Suc Zero) Zero = Just 0.12
Ex _ _ = Nothing

TEGraph : Type -> Type -> Type
TEGraph obj v = obj -> obj -> v -> Type

data EPath : {obj, r: Type}  -> (alg : Algebra (TwoOps r) r) -> EGraph obj r -> TEGraph obj r where
  Id : (EPath alg g) a a (alg Mulunit)
  Comp : {g : EGraph obj r} -> (EPath alg g) b c val' ->  (EPath alg g) a c (alg (Mul (g a b) (val)))

data EPath : {obj, r : Type} -> TEGraph obj r -> TEGraph obj (List r) where
  IdE : EPath g a a Nil
  CompE : {g : EGraph obj r} -> g a b v -> EPath g b c vs -> EPath g a c (v :: vs) 
  
T : (EPath Trop Ex) Zero Zero (Just 0.0)
T = Id

T' : (EPath Trop Ex) Zero (Suc Zero) (Just 1.0)
T' = Comp m1 Id


{-- 
data EPath : {obj, r : Type} -> TEGraph obj r -> TEGraph obj (List r) where
  IdE : EPath g a a Nil
  CompE : {g : EGraph obj r} -> g a b v -> EPath g b c vs -> EPath g a c (v :: vs) 
--}




--cob : (r : Type) -> (alg : Algebra (TwoOps r) r) -> (r -> Type) -> r
--cob r alg f = sumg where
--  g : DPair r f  -> r

--Eval : {obj, r : Type} -> (g : Egraph obj r) -> EPath alg g -> EGraph obj r
--Eval g epaths = if Inhabited(epaths a b v) then 
--(Eval g paths) a b = sum h where
--  h : DPair r (paths a b) -> List(r)

{-- 
Eval : (obj, r : Type) -> (g : TEGraph obj r) -> EPath g -> TEGraph obj r
Eval obj r g free = h where
  h : obj -> obj -> r
--}

