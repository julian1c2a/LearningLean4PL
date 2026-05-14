

inductive WTree where
 | sup (A : Type) (B : A → WTree) : WTree


-- Conjunto vacío (0 elementos)
def WTree.empty : WTree :=  WTree.sup Empty Empty.rec

-- Conjunto unitario (1 elemento)
def WTree.singleton (x : WTree) : WTree :=
  WTree.sup Unit (fun _ => x)

-- Conjunto finito (usando una lista/vector como mapeo subyacente o una función sobre Fin n)
-- Conjunto infinito numerable (ej: el conjunto de todos los naturales modelados como WSets)
-- Primero definimos el conjunto finito para cualquier ordinal n = {0, 1, ..., n-1}
-- Un conjunto de n elementos tiene n ramas (Fin n), y cada rama i apunta al ordinal i
def WTree.ofNat (n : Nat) : WTree :=
  WTree.sup (Fin n) (fun i => WTree.ofNat i.val)
termination_by n  -- Le decimos a Lean que esto no es un bucle infinito porque i.val < n

-- Conjunto infinito numerable (el ordinal omega = {0, 1, 2, ...})
-- Tiene infinitas ramas (Nat), y cada rama n apunta al ordinal finito n
def WTree.omega : WTree :=
  WTree.sup Nat WTree.ofNat

-- Representa un conjunto finito de naturales a partir de una lista
def WTree.fromListNat (L : List Nat) : WTree :=
  WTree.sup (Fin L.length) (fun i => WTree.ofNat (L.get i))

-- Ej: El conjunto {2, 5, 9}
def WTree.miConjuntoFinito : WTree :=
  WTree.fromListNat [2, 5, 9]

-- El conjunto {0, 2, 4, 6, 8, ...}
def WTree.pares : WTree :=
  WTree.sup Nat (fun n => WTree.ofNat (n * 2))

-- Construcción alternativa: ZFC (axiomas + conjuntos)
inductive ZFCSet where
| replace {α : Type} (f : α → ZFCSet) : ZFCSet -- axioma de reemplazamiento

-- El conjunto de los números naturales de Von Neumann dentro de ZFC
-- 0 = {} (conjunto vacío)
def ZFCSet.empty : ZFCSet :=
  ZFCSet.replace (α := Empty) Empty.rec

def ZFCSet.singleton (x : ZFCSet) : ZFCSet :=
  ZFCSet.replace (α := Unit) (fun _ => x)

-- Axioma de formación de pares: {a, b}
-- Creamos un conjunto con 2 elementos usando Bool (que tiene 2 valores: true/false)
def ZFCSet.pair (a b : ZFCSet) : ZFCSet :=
  ZFCSet.replace (α := Bool) (fun x => if x then a else b)

def ZFCSet.union (a b : ZFCSet) : ZFCSet :=
  match a, b with
  | ZFCSet.replace f, ZFCSet.replace g =>
    ZFCSet.replace (α := Sum _ _) (
      fun x =>
        match x with
        | Sum.inl i => f i
        | Sum.inr j => g j
    )
