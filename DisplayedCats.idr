

Graph : Type -> Type 
Graph obj = obj -> obj -> Type 

record GraphOver (g : Graph a) where
  constructor MkGraphOver
  totalgraph : Graph b
  fob : b -> a
  fmor : (x, y : b) -> totalgraph x y -> g (fob x) (fob y)

record DisplayGraph (baseGraph : Graph verts) where
    constructor MkDisplayGraph 
    dObj : verts -> Type
    dHom : (x, y : verts) -> baseGraph x y -> dObj x -> dObj y -> Type

natGraph : Nat -> Nat -> Type
natGraph n1 n2 = Nat

Map : natGraph 1 1 -> Nat
Map 0  = 1
Map (S n) = S (Map n)

Groth : (baseGraph : Graph verts) -> DisplayGraph baseGraph -> GraphOver baseGraph
Groth baseGraph (MkDisplayGraph dvert dedge) = MkGraphOver totalgraph fst emap where
  totalgraph : Graph (DPair verts dvert)
  totalgraph (MkDPair x a) (MkDPair y b) = DPair (baseGraph x y) (\f => dedge x y f a b)
  emap : (x, y : DPair verts dvert) -> totalgraph x y -> baseGraph (fst x) (fst y)
  emap x y (MkDPair f g) = f 


{-Groth : (baseGraph : Graph verts) -> DisplayGraph baseGraph -> GraphOver baseGraph
Groth baseGraph (MkDisplayGraph dvert dedge) = MkGraphOver totalgraph fst emap where
  totalgraph : Graph (DPair verts dvert)
  totalgraph (MkDPair x a) (MkDPair y b) = DPair (baseGraph x y) (\f => dedge x y f a b)
  emap : (x, y : DPair verts dvert) -> totalgraph x y -> baseGraph (fst x) (fst y)
  emap x y (?h) = ?f 


{-record DisplayGraph (baseObj : Type) where
    constructor MkDisplayGraph 
    baseGraph : Graph baseObj
    dObj : baseObj -> Type
    dHom : (x, y : baseObj) -> baseGraph x y -> dObj x -> dObj y -> Type

Graph : Type -> Type 
Graph obj = obj -> obj -> Type 

record Graph where
  constructor MkGraph 
  verts : Type
  edges : verts -> verts -> Type

record Cat (hom: Graph) where 
  constructor MkCat 
  identity : {a : verts @{hom}} -> edges @{hom} a a 
  composite : {a, b, c : verts} -> edges @{hom} b c -> edges @{hom} a b -> edges @{hom} a c

record GraphOver (g : Graph) where
  constructor MkGraphOver
  totalgraph : Graph
  fob : verts @{totalgraph} -> verts @{g}
  fmor : (x, y : verts @{totalgraph}) -> edges @{totalgraph} x y -> edges @{g} (fob x) (fob y)

record DisplayGraph (baseGraph : Graph) where
    constructor MkDisplayGraph 
    dObj : verts @{baseGraph} -> Type
    dHom : (x, y : verts @{baseGraph}) -> edges @{baseGraph} x y -> dObj x -> dObj y -> Type

Groth : (baseGraph : Graph) -> DisplayGraph baseGraph -> GraphOver baseGraph
Groth baseGraph (MkDisplayGraph dvert dedge) = MkGraphOver (MkGraph (DPair verts dvert) totaledges) fst emap where
  totaledges : (DPair verts dvert) -> (DPair verts dvert) -> Type
  totalgraph (MkDPair x a) (MkDPair y b) = MkDPair (edges @{baseGraph} x y) (\f => dedge x y f a b)
  emap : (x, y : DPair verts dvert) -> edges @{totalgraph} x y -> edges @{baseGraph} (fst x) (fst y)
  emap x y h = DPair.fst h 
 
{-InverseImage : (baseGraph : Graph verts) -> GraphOver baseGraph -> DisplayGraph baseGraph
InverseImage g fib = ?x

{-record DisplayCat (baseGraph : (Graph baseObj)) (dGraph : DisplayGraph baseGraph) (baseCat : Cat baseGraph) where
    constructor MkDisplayCat 
    dId : {a : baseObj} -> {x : dObj @{dGraph} a} -> dHom a a identity x x 
    dComp : {a, b, c : baseObj} -> {f : hom b c} -> {g : hom a b} -> {x : dObj a} -> {y : dObj b} -> {z : dObj c} -> dHom b c f y z -> dHom a b g x y -> dHom a c (composite f g) x z 







{-record DisplayCat (obj : Type) (hom : Cat obj) 
  constructor MkDisplayCat where
  dObj : obj -> Type 
  dHom : hom x y -> dObj x -> dObj y -> Type
 