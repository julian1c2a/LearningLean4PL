/-!
Sesión 5: Árbol Binario de Búsqueda y el tipo Set

Estructura del módulo:
  PARTE 1 — BST: el árbol binario de búsqueda (implementación interna)
  PARTE 2 — MiSet: el tipo conjunto (API pública)
  PARTE 3 — Instancias y notación
  PARTE 4 — Ejemplos
-/

-- ================================================================
-- PARTE 1: BST — ÁRBOL BINARIO DE BÚSQUEDA
-- ================================================================

namespace BST

-- Un árbol binario: o bien una hoja vacía, o un nodo con subárbol
-- izquierdo, un valor, y subárbol derecho.
-- Invariante BST (por convención, no impuesta por el tipo):
--   todo valor en el subárbol izquierdo < valor del nodo
--   todo valor en el subárbol derecho   > valor del nodo
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

-- Lean 4 tiene la typeclass Ord con compare : α → α → Ordering
-- donde Ordering = .lt | .eq | .gt  (comparación de tres vías)
-- En Haskell: class Ord a where compare :: a -> a -> Ordering

-- Insertar un elemento manteniendo la propiedad BST.
-- Si ya existe, no se duplica.
def insert [Ord α] (x : α) : Tree α → Tree α
  | Tree.leaf           => Tree.node Tree.leaf x Tree.leaf
  | Tree.node l v r     =>
      match compare x v with
      | Ordering.lt => Tree.node (insert x l) v r
      | Ordering.eq => Tree.node l v r   -- ya presente, sin cambio
      | Ordering.gt => Tree.node l v (insert x r)

-- Comprobar si un elemento está en el árbol.
def member [Ord α] (x : α) : Tree α → Bool
  | Tree.leaf       => false
  | Tree.node l v r =>
      match compare x v with
      | Ordering.lt => member x l
      | Ordering.eq => true
      | Ordering.gt => member x r

-- Recorrido en orden (in-order): devuelve los elementos ORDENADOS.
-- Esta propiedad es clave: para un BST válido, toList da una lista ordenada.
def toList : Tree α → List α
  | Tree.leaf       => []
  | Tree.node l v r => toList l ++ [v] ++ toList r

-- Construir un árbol desde una lista.
def fromList [Ord α] (xs : List α) : Tree α :=
  xs.foldl (fun t x => insert x t) Tree.leaf

-- Número de elementos (nodos internos).
def size : Tree α → Nat
  | Tree.leaf       => 0
  | Tree.node l _ r => 1 + size l + size r

-- Altura del árbol.
def height : Tree α → Nat
  | Tree.leaf       => 0
  | Tree.node l _ r => 1 + max (height l) (height r)

-- Mínimo y máximo de un BST no vacío (Option para el caso vacío).
def minElem : Tree α → Option α
  | Tree.leaf           => none
  | Tree.node Tree.leaf v _ => some v
  | Tree.node l _ _     => minElem l

def maxElem : Tree α → Option α
  | Tree.leaf             => none
  | Tree.node _ v Tree.leaf => some v
  | Tree.node _ _ r       => maxElem r

end BST

-- Verificaciones rápidas del BST:
private def arbolEj := BST.fromList [5, 3, 8, 1, 4, 7, 9]

#eval BST.toList arbolEj     -- [1, 3, 4, 5, 7, 8, 9]  (ordenado)
#eval BST.member 4 arbolEj   -- true
#eval BST.member 6 arbolEj   -- false
#eval BST.size arbolEj       -- 7
#eval BST.height arbolEj     -- 3
#eval BST.minElem arbolEj    -- some 1
#eval BST.maxElem arbolEj    -- some 9

-- ================================================================
-- PARTE 2: MiSet — EL TIPO CONJUNTO
-- ================================================================
-- Encapsulamos el BST en una estructura opaca.
-- Los usuarios trabajan con MiSet, sin saber que hay un árbol dentro.

structure MiSet (α : Type) where
  private tree : BST.Tree α

namespace MiSet

-- Conjunto vacío.
def empty : MiSet α :=
  { tree := BST.Tree.leaf }

-- Insertar un elemento (sin duplicados, garantizado por el BST).
def insert [Ord α] (x : α) (s : MiSet α) : MiSet α :=
  { tree := BST.insert x s.tree }

-- Comprobar pertenencia.
def member [Ord α] (x : α) (s : MiSet α) : Bool :=
  BST.member x s.tree

-- Lista de elementos (siempre en orden ascendente).
def toList (s : MiSet α) : List α :=
  BST.toList s.tree

-- Construir un conjunto desde una lista (elimina duplicados).
def fromList [Ord α] (xs : List α) : MiSet α :=
  { tree := BST.fromList xs }

-- Número de elementos.
def size (s : MiSet α) : Nat :=
  BST.size s.tree

-- Conjunto vacío?
def isEmpty (s : MiSet α) : Bool :=
  s.size == 0

-- Unión: todos los elementos de s1 y s2.
def union [Ord α] (s1 s2 : MiSet α) : MiSet α :=
  s1.toList.foldl (fun acc x => acc.insert x) s2

-- Intersección: sólo los elementos presentes en ambos.
def intersection [Ord α] (s1 s2 : MiSet α) : MiSet α :=
  s1.toList.foldl
    (fun acc x => if s2.member x then acc.insert x else acc)
    MiSet.empty

-- Diferencia: elementos de s1 que no están en s2.
def difference [Ord α] (s1 s2 : MiSet α) : MiSet α :=
  s1.toList.foldl
    (fun acc x => if s2.member x then acc else acc.insert x)
    MiSet.empty

-- Subconjunto: ¿todos los elementos de s1 están en s2?
def subset [Ord α] (s1 s2 : MiSet α) : Bool :=
  s1.toList.all s2.member

-- Imagen: aplicar una función a todos los elementos.
def map [Ord β] (f : α → β) (s : MiSet α) : MiSet β :=
  MiSet.fromList (s.toList.map f)

-- Filtrar elementos que cumplan un predicado.
def filter [Ord α] (p : α → Bool) (s : MiSet α) : MiSet α :=
  MiSet.fromList (s.toList.filter p)

end MiSet

-- ================================================================
-- PARTE 3: INSTANCIAS Y NOTACIÓN
-- ================================================================

-- ToString: muestra el conjunto como {1, 2, 3}
instance [ToString α] : ToString (MiSet α) where
  toString s :=
    let elems := s.toList.map toString
    let inner := elems.foldl
      (fun acc x => if acc == "" then x else acc ++ ", " ++ x) ""
    "{" ++ inner ++ "}"

-- BEq: dos conjuntos son iguales si tienen los mismos elementos.
-- Como toList devuelve la lista ordenada, basta comparar las listas.
instance [Ord α] [BEq α] : BEq (MiSet α) where
  beq s1 s2 := s1.toList == s2.toList

-- Membership y notación ∈
--
-- La typeclass Membership de Lean 4 usa `outParam` en el tipo elemento,
-- lo que crea una ambigüedad cuando ese tipo también aparece como parámetro
-- del contenedor (MiSet β). Lo resolvemos con un helper explícito:
-- Nota: en Lean 4, Membership.mem toma (contenedor, elemento),
-- es decir mem : γ → α → Prop, al contrario del orden intuitivo.
-- x ∈ s se expande a Membership.mem s x.
instance [Ord α] : Membership α (MiSet α) where
  mem s x := MiSet.member x s = true

-- Decidable para usar ∈ en if/match:
instance [Ord α] {x : α} {s : MiSet α} : Decidable (x ∈ s) :=
  show Decidable (MiSet.member x s = true) from
    if h : MiSet.member x s = true then .isTrue h else .isFalse h

-- ================================================================
-- PARTE 4: EJEMPLOS
-- ================================================================

def s1 : MiSet Nat := MiSet.fromList [3, 1, 4, 1, 5, 9, 2, 6]
def s2 : MiSet Nat := MiSet.fromList [2, 7, 1, 8, 2, 8]

#eval s!"s1 = {s1}"                        -- {1, 2, 3, 4, 5, 6, 9}
#eval s!"s2 = {s2}"                        -- {1, 2, 7, 8}
#eval s!"s1 ∪ s2 = {s1.union s2}"         -- {1, 2, 3, 4, 5, 6, 7, 8, 9}
#eval s!"s1 ∩ s2 = {s1.intersection s2}"  -- {1, 2}
#eval s!"s1 \\ s2 = {s1.difference s2}"   -- {3, 4, 5, 6, 9}
#eval s!"s1 ⊆ s2? {s1.subset s2}"         -- false
#eval s!"3 ∈ s1? {MiSet.member 3 s1}"     -- true

-- Con la notación ∈ en un if:
def mensaje (n : Nat) (s : MiSet Nat) : String :=
  if n ∈ s then s!"{n} está en el conjunto"
  else s!"{n} no está en el conjunto"

#eval mensaje 5 s1   -- "5 está en el conjunto"
#eval mensaje 7 s1   -- "7 no está en el conjunto"

-- map y filter:
#eval s!"pares de s1 = {s1.filter (· % 2 == 0)}"    -- {2, 4, 6}
#eval s!"s1 × 2    = {s1.map (· * 2)}"              -- {2, 4, 6, 8, 10, 12, 18}

-- BEq: conjuntos con los mismos elementos son iguales aunque
-- se insertaran en distinto orden:
def s3 := MiSet.fromList [9, 5, 4, 1, 6, 2, 3]
#eval s1 == s3   -- true

-- ================================================================
-- MAIN
-- ================================================================

def main : IO Unit := do
  IO.println "=== Sesión 5: BST y MiSet ==="
  IO.println s!"s1          = {s1}"
  IO.println s!"s2          = {s2}"
  IO.println s!"s1 ∪ s2     = {s1.union s2}"
  IO.println s!"s1 ∩ s2     = {s1.intersection s2}"
  IO.println s!"s1 \\ s2    = {s1.difference s2}"
  IO.println s!"pares de s1 = {s1.filter (· % 2 == 0)}"
  IO.println s!"5 ∈ s1?     {mensaje 5 s1}"
  IO.println s!"7 ∈ s1?     {mensaje 7 s1}"
  IO.println s!"s1 == s3?   {s1 == s3}"
