/-!
Sesión 6: Árboles Balanceados

PARTE 1 — Red-Black Tree (Okasaki): algoritmo de balanceo en tiempo de ejecución
PARTE 2 — AVL indexado por altura: invariante de balance impuesta por el TIPO
PARTE 3 — Comparación BST plano vs RBTree
-/

-- ================================================================
-- PARTE 1: RED-BLACK TREE (Okasaki, 1998)
-- ================================================================
--
-- Invariantes Red-Black:
--   (R1) Cada nodo es Rojo o Negro
--   (R2) La raíz es siempre Negra
--   (R3) Un nodo Rojo sólo tiene hijos Negros (no hay dos Rojos consecutivos)
--   (R4) Todos los caminos desde la raíz hasta una hoja tienen la misma
--        "altura negra" (número de nodos Negros)
--
-- Estas invariantes garantizan altura O(log n).
-- Okasaki observó que la función `balance` captura los 4 casos de
-- violación de (R3) de forma simétrica y elegante.

inductive Color where | R | B deriving BEq, Repr

inductive RBTree (α : Type) where
  | empty : RBTree α
  | node  : Color → RBTree α → α → RBTree α → RBTree α
  deriving Repr

namespace RBTree

-- balance: repara violaciones rojo-rojo en un nodo NEGRO.
-- Los 4 casos son rotaciones simétricas; todos producen el mismo resultado:
-- un nodo rojo con dos hijos negros.
--
--    Caso 1 (izq-izq):        Caso 2 (izq-der):
--        z[B]                     z[B]
--       /    \                   /    \
--     y[R]    d               x[R]    d
--    /    \                  /    \
--  x[R]    c                a    y[R]
--  /  \                         /  \
-- a    b                       b    c
--
--    Caso 3 (der-izq):        Caso 4 (der-der):
--      x[B]                    x[B]
--     /    \                  /    \
--    a    z[R]               a    y[R]
--        /    \                   /  \
--      y[R]   d                  b   z[R]
--      /  \                          /  \
--     b    c                        c    d
--
-- Los 4 casos producen:
--        y[R]
--       /    \
--     x[B]   z[B]
--    /   \  /   \
--   a    b c    d

def balance : Color → RBTree α → α → RBTree α → RBTree α
  -- caso izq-izq
  | .B, .node .R (.node .R a x b) y c, z, d =>
      .node .R (.node .B a x b) y (.node .B c z d)
  -- caso izq-der
  | .B, .node .R a x (.node .R b y c), z, d =>
      .node .R (.node .B a x b) y (.node .B c z d)
  -- caso der-izq
  | .B, a, x, .node .R (.node .R b y c) z d =>
      .node .R (.node .B a x b) y (.node .B c z d)
  -- caso der-der
  | .B, a, x, .node .R b y (.node .R c z d) =>
      .node .R (.node .B a x b) y (.node .B c z d)
  -- sin violación
  | c, l, x, r => .node c l x r

-- Inserción auxiliar: inserta como BST usando balance para reparar.
-- El resultado puede ser un árbol rojo con hijo rojo (se pinta negro arriba).
def insertAux [Ord α] (x : α) : RBTree α → RBTree α
  | .empty         => .node .R .empty x .empty
  | .node c l v r  =>
      match compare x v with
      | .lt => balance c (insertAux x l) v r
      | .eq => .node c l v r
      | .gt => balance c l v (insertAux x r)

-- Inserción pública: garantiza que la raíz sea siempre Negra (invariante R2).
def insert [Ord α] (x : α) (t : RBTree α) : RBTree α :=
  match insertAux x t with
  | .node _ l v r => .node .B l v r   -- fuerza raíz negra
  | .empty        => .empty

def member [Ord α] (x : α) : RBTree α → Bool
  | .empty        => false
  | .node _ l v r =>
      match compare x v with
      | .lt => member x l
      | .eq => true
      | .gt => member x r

def toList : RBTree α → List α
  | .empty        => []
  | .node _ l v r => toList l ++ [v] ++ toList r

def fromList [Ord α] (xs : List α) : RBTree α :=
  xs.foldl (fun t x => insert x t) .empty

def size : RBTree α → Nat
  | .empty        => 0
  | .node _ l v r => 1 + size l + size r

def height : RBTree α → Nat
  | .empty        => 0
  | .node _ l v r => 1 + max (height l) (height r)

-- Altura negra: todos los caminos deben dar el mismo valor (invariante R4).
-- Devuelve none si se viola la invariante.
def blackHeight : RBTree α → Option Nat
  | .empty           => some 0
  | .node c l _ r    =>
      match blackHeight l, blackHeight r with
      | some hl, some hr =>
          if hl == hr then
            some (hl + if c == .B then 1 else 0)
          else none
      | _, _ => none

instance [ToString α] : ToString (RBTree α) where
  toString t :=
    let elems := t.toList.map toString
    let inner := elems.foldl (fun acc x => if acc == "" then x else acc ++ ", " ++ x) ""
    "RBT{" ++ inner ++ "}"

end RBTree

-- Verificaciones:
private def rb1 := RBTree.fromList [5, 3, 8, 1, 4, 7, 9, 2, 6]
private def rb2 := RBTree.fromList (List.range 10)  -- caso peor para BST plano

#eval s!"{rb1}"                    -- RBT{1, 2, 3, 4, 5, 6, 7, 8, 9}
#eval RBTree.height rb1            -- ≤ 2·log₂(10) ≈ 7
#eval RBTree.blackHeight rb1       -- some n  (invariante R4 ✓)
#eval RBTree.member 4 rb1          -- true
#eval RBTree.member 10 rb1         -- false

-- ================================================================
-- PARTE 2: AVL INDEXADO POR ALTURA
-- ================================================================
--
-- Podemos imponer la invariante AVL EN EL TIPO usando índices.
-- `AVL α h` sólo puede construirse si el árbol tiene altura h
-- y está balanceado (diferencia de alturas ≤ 1 en cada nodo).
--
-- Para codificar la diferencia de alturas usamos un tipo auxiliar:

-- Diferencia de alturas permitida entre subárboles:
-- `Bal lh rh h` significa: altura izq=lh, alt der=rh, altura total=h, |lh-rh|≤1
inductive Bal : Nat → Nat → Nat → Prop where
  | leftH  : Bal (n+1) n     (n+2)  -- izquierdo 1 más alto
  | equal  : Bal n     n     (n+1)  -- iguales
  | rightH : Bal n     (n+1) (n+2)  -- derecho 1 más alto

-- El árbol AVL indexado por altura:
-- `AVL α h` es un árbol BST balanceado de altura h.
-- El compilador rechaza árboles que violen la invariante.
inductive AVL (α : Type) : Nat → Type where
  | leaf : AVL α 0
  | node : Bal lh rh h → AVL α lh → α → AVL α rh → AVL α h

-- Búsqueda: igual que en BST, pero el tipo garantiza que el árbol es válido.
def AVL.member [Ord α] (x : α) : AVL α h → Bool
  | .leaf            => false
  | .node _ l v r    =>
      match compare x v with
      | .lt => AVL.member x l
      | .eq => true
      | .gt => AVL.member x r

-- Podemos construir AVLs válidos manualmente:
-- Árbol de altura 1: un solo nodo
def avlSingle (x : α) : AVL α 1 :=
  .node .equal .leaf x .leaf

-- Árbol de altura 2: nodo con hijo izquierdo
def avlTwo (x y : α) : AVL α 2 :=
  .node .leftH (.node .equal .leaf x .leaf) y .leaf

-- El compilador rechaza esto (descomenta para ver el error de tipo):
-- def avlMal : AVL Nat 1 :=
--   .node .equal (.node .equal .leaf 1 .leaf) 2 (.node .equal .leaf 3 .leaf)
--   -- Error: espera AVL Nat 1 pero produce AVL Nat 2

-- Búsqueda en los AVLs:
#eval AVL.member 1 (avlTwo 1 2)   -- true
#eval AVL.member 3 (avlTwo 1 2)   -- false

-- Nota: implementar `insert` para AVL indexado requiere devolver
-- un tipo que refleje si el árbol "creció" o no:
--
--   inductive Grew (α : Type) (h : Nat) where
--     | same  : AVL α h     → Grew α h
--     | taller: AVL α (h+1) → Grew α h
--
-- y manejar las 4 rotaciones con pruebas de tipo. Esto es avanzado
-- y lo dejaremos para cuando veamos tácticas.

-- ================================================================
-- PARTE 3: COMPARACIÓN BST PLANO vs RBTree
-- ================================================================

-- El peor caso para un BST plano es una lista ordenada → árbol degenerado.
-- El RBTree mantiene altura O(log n) incluso en ese caso.

namespace BST
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

def insert [Ord α] (x : α) : Tree α → Tree α
  | .leaf         => .node .leaf x .leaf
  | .node l v r   =>
      match compare x v with
      | .lt => .node (insert x l) v r
      | .eq => .node l v r
      | .gt => .node l v (insert x r)

def fromList [Ord α] (xs : List α) : Tree α :=
  xs.foldl (fun t x => insert x t) .leaf

def height : Tree α → Nat
  | .leaf       => 0
  | .node l _ r => 1 + max (height l) (height r)
end BST

-- Insertar [0..15] en orden (peor caso):
private def nElems := 16
private def listaOrdenada := List.range nElems

private def bstPlano := BST.fromList listaOrdenada
private def rbBalanceado := RBTree.fromList listaOrdenada

#eval s!"BST plano  altura: {BST.height bstPlano}"     -- 16 (lista)
#eval s!"RBTree     altura: {RBTree.height rbBalanceado}" -- ~5 (balanceado)
#eval s!"RBTree bh:         {RBTree.blackHeight rbBalanceado}" -- some n

-- ================================================================
-- MAIN
-- ================================================================

def main : IO Unit := do
  IO.println "=== Sesión 6: Árboles Balanceados ==="
  IO.println s!"RBTree {nElems} elems ordenados:"
  IO.println s!"  altura BST plano = {BST.height bstPlano}"
  IO.println s!"  altura RBTree    = {RBTree.height rbBalanceado}"
  IO.println s!"  altura negra     = {RBTree.blackHeight rbBalanceado}"
  IO.println s!"  contenido: {rb1}"
