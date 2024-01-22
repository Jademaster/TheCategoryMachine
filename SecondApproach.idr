import SemiringsAndMatrices

-- a graph enriched in r is a square matrix valued in r
EGraph : (r : Type) -> Type
EGraph r ={ n : Nat } -> Matrix n n r

--the free enriched category is the free monoid w.r.t. the matrix algebra
FreeECat : {n : Nat} -> {r : Type} -> Algebra (TwoOps (Matrix n n r)) (Matrix n n r) -> EGraph r -> EGraph r
FreeECat {n=n} {r=r} matalg g = matalg (Mul g (matalg (Add matalg(Addunit) (FreeECat matalg g))))

guard : Eq a => (a -> a) -> a -> a 
guard f accum = if f a == a then a else repeat f (f a)

-- data KleeneF : twoops op1 op2 op3, kleeneStar : a -> KleeneF a x 


freeKleene : Algebra (TwoOps a) a -> Algebra (Kleene a) a 
freeKleene ... 
freeKlene alg (Star x) = ?guardGoesHere (alg Mult x (Star x)  (alg MulUnit))

kleeneMatrix : Algebra (Kleene a) a -> Algebra (Kleene (Matrix n n a)) -> Matrx n n a 

Kleene a = Mu (KleeneF a)
formula : Matrix n n a -> Kleene (Matrix n n a)

formula m1 = Star m1 

mult : Algebra (TwoOps a) a => Matrix n n a -> Matrix n n a -> Matrix n n a 
mult alg m1 accum = 

data Fix : (Type -> Type) -> Type where 
  In : f (Fix f) -> Fix f 

out : Mu f -> f (Mu f) 
out (In m) = m 

data Free : (Type -> Type) -> Type -> Type where 
  Var : a -> Free f a 
  Join : f (Free f a) -> Free f a  

data SemiringSig : Nat -> Type where 
  Zero : SemiringSig 0 
  One : SemiringSig 0 
  Mult : SemiringSig 2 
  Add : SemiringSig 2 
  
toSig : Algebra (TwoOps a) a -> FinAlg SemiringSig n 

data Op : (Nat ->  Type) -> Nat -> Type where 
  Var : Fin n -> Op f n 
  Bind : f n -> (Fin n -> Op f m) -> Op f m  

-- initial algebra
cata : Algebra f c -> Fix f -> c 
-- free algera
eval : (a -> c) -> Algebra f a -> Free f a -> c 
-- free operad
eval : (Fin n -> c) -> KanAlgebra f c -> Op f n -> c 

-- data Op : (Nat -> Nat -> Type) -> Nat -> Nat -> Type where 
--  Var : Fin n  -> Op f n 
  --Bind : f n m -> (Fin m -> Op f n l) -> Op f m  
--  Trace : Op f (m + c) (n + c) -> Op f m n 

example : Op SemiringSig 2 
example = Bind Add (\i => case i of 
  FZ => Var FZ
  FS FZ => Var (FS FZ))


codata Cofree : (Type -> Type) -> Type -> Type where 
  Mk : (a, (Cofree f a)) -> f (Cofree f a)

data Stream : Type -> Type where 
  Next : Stream a -> Stream a  
-- wont work 
codata Stream : Type -> Type where 
  Head : Stream a -> a 
  Tail : Stream a -> Stream a 
  

Free f () = Fix f = Mu f 
Cofree f Void = Fix f = Nu f 

cata : (f a -> a) -> Fix f -> a
ana : (a -> f a) -> a -> Fix f
cataM : Monad m => (f a -> a) -> Mu f -> m a


data Automaton m s a = Automaton
  { initial    :: s               -- ^ Initial State
  , transition :: s -> (a -> m s)   -- ^ Change state with a context.
  , accepting  :: s -> Bool       -- ^ Accepting subset as a predicate.
  }

Automaton : (Type -> Type) -> Type -> Type -> Type 
Automaton m a s = (s -> (a -> m s, Bool))


data StreamF : Type -> Type -> Type where 
  Step : a -> x -> StreamF a x 

StreamF' : Type -> Type -> Type  
StreamF' a x = (a, x)

Stream : Type -> Type 
Stream a = Fix (StreamF a)

-- ana : (a -> f a) -> a -> Fix f

Final : Type -> Type 
Final a = Fix (Automaton' a)

Automaton' : Type -> Type -> Type 
Automaton' a s = (s -> (a -> s))

AutomatonAlg : Type -> Type -> Type 
AutomatonAlg a s = (a, s) -> s

initial : (AutomatonAlg a s -> a) -> Fix (AutomatonAlg a) -> s
initial = cata
 
final : (s -> (a -> s)) -> s -> Final a 
final = ana 

-- run : (s -> a -> s) -> List a -> s -> s
-- Eq : a -> a -> Bool 
-- DecEq : (x : a) -> (y : a) -> DecEq x == y 

--bisim : DecEq s, DecEq f s => DecEq (Fix f s)

run : Automaton' s a -> List a -> s
run = fold 
