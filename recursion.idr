data Mu : (pattern : Type -> Type) -> Type where
    In : {f: Type -> Type} -> f (Mu f) -> Mu f

Algebra : (Type -> Type) -> Type -> Type  
Algebra f a = f a -> a

cata : Functor f => Algebra f a -> Mu f -> a
cata alg (In op) = alg (map (cata alg) op)

