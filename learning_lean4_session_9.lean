<<<<<<< HEAD
-- Definición de HFSets y listas (basado en AczelSetTheory)
inductive CList : Type where
  | mk : List CList → CList
  deriving Repr, Inhabited

namespace CList

inductive CListOp
| mem
| subset
| eq

@[simp]
def opWeight : CListOp → Nat
| .mem    => 0
| .subset => 1
| .eq     => 2

set_option linter.unusedSimpArgs false in
def evalOp (op : CListOp) (A B : CList) : Bool :=
  match op, A, B with
  | .mem, _, mk []          => false
  | .mem, x, mk (y :: ys)   =>
      evalOp .eq x y || evalOp .mem x (mk ys)
  | .subset, mk [], _       => true
  | .subset, mk (x :: xs), B =>
      evalOp .mem x B && evalOp .subset (mk xs) B
  | .eq, A, B               =>
      evalOp .subset A B && evalOp .subset B A
termination_by (((sizeOf A + sizeOf B : Nat) * 3) + opWeight op : Nat)
decreasing_by
  all_goals simp_wf
  all_goals try simp [opWeight, sizeOf]
  all_goals try omega

def extEq (A B : CList) : Bool := evalOp .eq A B

theorem extEq_refl (A : CList) : extEq A A = true := sorry
theorem extEq_symm {A B : CList} (h : extEq A B = true) : extEq B A = true := sorry
theorem extEq_trans {A B C : CList} (h1 : extEq A B = true) (h2 : extEq B C = true) : extEq A C = true := sorry

def Setoid : Setoid CList where
  r A B := extEq A B = true
  iseqv := {
    refl := extEq_refl
    symm := fun h => extEq_symm h
    trans := fun h1 h2 => extEq_trans h1 h2
  }

end CList

-- Finalmente, el tipo HFSet
def HFSet : Type 0 := Quotient CList.Setoid

inductive NextLevel (Base : Type u) : Type u where
| inj : Base → NextLevel Base
-- Constructores de comprensión
| ext : (Base → Bool) → NextLevel Base
| dif : (Base → Bool) → NextLevel Base
-- Axiomas estructurales
| pair : NextLevel Base → NextLevel Base → NextLevel Base
| union : NextLevel Base → NextLevel Base → NextLevel Base
| inter : NextLevel Base → NextLevel Base → NextLevel Base
| sUnion : NextLevel Base → NextLevel Base
| sInter : NextLevel Base → NextLevel Base
-- EL PRODUCTO CARTESIANO GENERALIZADO (Por funciones índice)
| cartProdIdx : Base → (Base → NextLevel Base) → NextLevel Base

-- La jerarquía infinita ahora vive toda en el Universo 0
def AType : Nat → Type 0
| 0     => HFSet
| n + 1 => NextLevel (AType n)

-- ==========================================
-- COERCIONES (Inyecciones Automáticas)
-- ==========================================
instance coe_AType_next {n : Nat} : Coe (AType n) (AType (n + 1)) where
    coe x := NextLevel.inj x

-- ==========================================
-- EL SETOIDE (Relación de Equivalencia)
-- ==========================================
-- Definimos una relación que le dice a Lean cuándo dos "árboles"
-- distintos deben considerarse el mismo conjunto matemático.
inductive SetEquiv {Base : Type u} : NextLevel Base → NextLevel Base → Prop where
-- 1. Propiedades obligatorias de toda equivalencia
| refl (x : NextLevel Base) : SetEquiv x x
| symm {x y : NextLevel Base} : SetEquiv x y → SetEquiv y x
| trans {x y z : NextLevel Base} : SetEquiv x y → SetEquiv y z → SetEquiv x z
-- 2. Axiomas de Extensionalidad de Conjuntos
-- El orden en un par no importa: {x, y} == {y, x}
| pair_comm (x y : NextLevel Base) :SetEquiv (NextLevel.pair x y) (NextLevel.pair y x)
-- Conmutatividad de la unión: A U B == B U A
| union_comm (x y : NextLevel Base) :SetEquiv (NextLevel.union x y) (NextLevel.union y x)
-- Asociatividad de la unión: (A U B) U C == A U (B U C)
| union_assoc (x y z : NextLevel Base) :SetEquiv (NextLevel.union (NextLevel.union x y) z) (NextLevel.union x (NextLevel.union y z))
-- Idempotencia de la unión: A U A == A
| union_idemp (x : NextLevel Base) :SetEquiv (NextLevel.union x x) x

-- Agrupamos las pruebas de que es una Relación de Equivalencia pura
def setEquiv_isequiv {Base : Type u} : Equivalence (@SetEquiv Base) :=
{
    refl  := SetEquiv.refl,
    symm  := SetEquiv.symm,
    trans := SetEquiv.trans
}

-- Registramos la instancia oficial de Setoid en Lean
instance nextLevelSetoid {Base : Type u} : Setoid (NextLevel Base) where
    r     := SetEquiv
    iseqv := setEquiv_isequiv

-- ==========================================
-- EL COCIENTE (El Verdadero Universo Matemático)
-- ==========================================
-- QNextLevel (Quotient Next Level) colapsa todos los árboles equivalentes.
-- A partir de aquí, las representaciones sintácticas desaparecen y
-- solo queda la "esencia" del conjunto matemático.
def QNextLevel (Base : Type u) : Type u := Quotient (@nextLevelSetoid Base)

-- Ejemplo (comentado): cómo se usa. La notación ⟦x⟧ proyecta un árbol al cociente.
-- variable {Base : Type u} (A B : NextLevel Base)
-- #check (⟦NextLevel.union A B⟧ : QNextLevel Base)
=======
/-!
Sesión 9: Bosque de Universos (Type u) con árboles de tipos por nivel

Idea del diseño:
  - En runtime no podemos manipular directamente `u` como dato de `Type u`.
  - Por eso representamos cada universo con una etiqueta `Nat` (nivel).
  - Cada nivel `u` tiene su propio árbol FINITO de descriptores de tipos.

Estructura:
  PARTE 1 — Árbol n-ario de descriptores de tipos (TypeTree)
  PARTE 2 — Bucket por nivel de universo (UniverseBucket)
  PARTE 3 — Lista ordenada de buckets (UniverseForest)
  PARTE 4 — Ejemplos
-/

-- ================================================================
-- PARTE 1: TypeTree — árbol de descriptores de tipos
-- ================================================================

namespace TypeTree

/--
`TypeNode` representa un tipo por nombre y una lista finita de subtipos/hijos.
No es el `Type u` real, sino su descriptor runtime-friendly.
-/
structure TypeNode where
  name     : String
  children : List TypeNode
  deriving Repr, BEq

abbrev TypeTree := List TypeNode

/-- Inserta un nodo por nombre manteniendo orden lexicográfico y sin duplicados. -/
def insertNodeByName (newNode : TypeNode) : TypeTree → TypeTree
  | [] => [newNode]
  | n :: ns =>
      match compare newNode.name n.name with
      | .lt => newNode :: n :: ns
      | .eq => n :: ns
      | .gt => n :: insertNodeByName newNode ns

/-- Inserta un tipo hoja (sin hijos) por nombre. -/
def insertTypeName (typeName : String) (tree : TypeTree) : TypeTree :=
  insertNodeByName { name := typeName, children := [] } tree

/-- Busca si existe un nombre de tipo en el nivel actual del árbol (raíz del bosque local). -/
def containsTypeName (typeName : String) : TypeTree → Bool
  | [] => false
  | n :: ns =>
      match compare typeName n.name with
      | .lt => false
      | .eq => true
      | .gt => containsTypeName typeName ns

/-- Convierte el árbol local a lista de nombres (nivel raíz). -/
def rootNames (tree : TypeTree) : List String :=
  tree.map (·.name)

end TypeTree

-- ================================================================
-- PARTE 2: UniverseBucket — un nivel u con su árbol de tipos
-- ================================================================

structure UniverseBucket where
  level : Nat
  types : TypeTree.TypeTree
  deriving Repr

namespace UniverseBucket

/-- Crea un bucket vacío para un nivel concreto. -/
def empty (u : Nat) : UniverseBucket :=
  { level := u, types := [] }

/-- Inserta un descriptor de tipo en el bucket. -/
def insertType (typeName : String) (b : UniverseBucket) : UniverseBucket :=
  { b with types := TypeTree.insertTypeName typeName b.types }

/-- Pertenencia de un descriptor de tipo en el bucket. -/
def containsType (typeName : String) (b : UniverseBucket) : Bool :=
  TypeTree.containsTypeName typeName b.types

end UniverseBucket

-- ================================================================
-- PARTE 3: UniverseForest — lista ordenada por nivel u
-- ================================================================

abbrev UniverseForest := List UniverseBucket

namespace UniverseForest

/-- Bosque vacío (sin niveles aún). -/
def empty : UniverseForest := []

/--
Inserta un bucket en orden por nivel.
Si ya existe el nivel, no duplica.
-/
def insertBucket (b : UniverseBucket) : UniverseForest → UniverseForest
  | [] => [b]
  | x :: xs =>
      match compare b.level x.level with
      | .lt => b :: x :: xs
      | .eq => x :: xs
      | .gt => x :: insertBucket b xs

/-- Garantiza que el nivel u exista, creando bucket vacío si falta. -/
def ensureLevel (u : Nat) (f : UniverseForest) : UniverseForest :=
  insertBucket (UniverseBucket.empty u) f

/--
Inserta un descriptor de tipo en el nivel `u`.
Si el nivel no existe, lo crea.
-/
def insertTypeAtLevel (u : Nat) (typeName : String) : UniverseForest → UniverseForest
  | [] => [ (UniverseBucket.empty u).insertType typeName ]
  | b :: bs =>
      match compare u b.level with
      | .lt => (UniverseBucket.empty u).insertType typeName :: b :: bs
      | .eq => b.insertType typeName :: bs
      | .gt => b :: insertTypeAtLevel u typeName bs

/-- Devuelve el bucket del nivel `u` si existe. -/
def findLevel (u : Nat) : UniverseForest → Option UniverseBucket
  | [] => none
  | b :: bs =>
      match compare u b.level with
      | .lt => none
      | .eq => some b
      | .gt => findLevel u bs

/-- Comprueba si un tipo está en el nivel `u`. -/
def containsAtLevel (u : Nat) (typeName : String) (f : UniverseForest) : Bool :=
  match findLevel u f with
  | none => false
  | some b => b.containsType typeName

/-- Lista de niveles presentes (ordenados). -/
def levels (f : UniverseForest) : List Nat :=
  f.map (·.level)

/-- Vista amigable: `(u, [tipos])` por cada bucket. -/
def snapshot (f : UniverseForest) : List (Nat × List String) :=
  f.map (fun b => (b.level, TypeTree.rootNames b.types))

end UniverseForest

-- ================================================================
-- PARTE 4: EJEMPLOS
-- ================================================================

-- Tu idea: no tienen por qué estar todos los u intermedios.
-- Insertamos primero en u=0, luego aparece u=2, y más tarde u=1.
def universoEj : UniverseForest :=
  UniverseForest.empty
    |> UniverseForest.insertTypeAtLevel 0 "Nat"
    |> UniverseForest.insertTypeAtLevel 0 "List Nat"
    |> UniverseForest.insertTypeAtLevel 2 "Type 1"
    |> UniverseForest.insertTypeAtLevel 1 "Type 0"
    |> UniverseForest.insertTypeAtLevel 0 "Bool"

#eval UniverseForest.levels universoEj
-- esperado: [0, 1, 2]

#eval UniverseForest.snapshot universoEj
-- esperado (ordenado por nivel y por nombre dentro del nivel):
-- [(0, ["Bool", "List Nat", "Nat"]), (1, ["Type 0"]), (2, ["Type 1"])]

#eval UniverseForest.containsAtLevel 0 "Nat" universoEj     -- true
#eval UniverseForest.containsAtLevel 0 "Int" universoEj     -- false
#eval UniverseForest.containsAtLevel 2 "Type 1" universoEj  -- true
#eval UniverseForest.containsAtLevel 3 "Type 2" universoEj  -- false

-- Un ejemplo adicional: saltando niveles (0 y 4 solamente)
def universoSalto : UniverseForest :=
  UniverseForest.empty
    |> UniverseForest.insertTypeAtLevel 4 "HugeType"
    |> UniverseForest.insertTypeAtLevel 0 "BaseType"

#eval UniverseForest.levels universoSalto   -- [0, 4]
#eval UniverseForest.snapshot universoSalto -- [(0, ["BaseType"]), (4, ["HugeType"])]

-- ================================================================
-- MAIN
-- ================================================================

def main : IO Unit := do
  IO.println "=== Sesión 9: Bosque de Universos ==="
  IO.println s!"niveles(universoEj) = {UniverseForest.levels universoEj}"
  IO.println s!"snapshot(universoEj) = {UniverseForest.snapshot universoEj}"
  IO.println s!"Nat en u0? {UniverseForest.containsAtLevel 0 "Nat" universoEj}"
  IO.println s!"Type 1 en u2? {UniverseForest.containsAtLevel 2 "Type 1" universoEj}"
>>>>>>> faeae1ce6e7c998c1180ad7257e112760e098b98
