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
  all_goals try simp [sizeOf]
  all_goals try omega

def extEq (A B : CList) : Bool := evalOp .eq A B
def subset (A B : CList) : Bool := evalOp .subset A B
def mem (x A : CList) : Bool := evalOp .mem x A

-- ─────────────────────────────────────────────────────────────────
-- Lemas auxiliares booleanos
-- ─────────────────────────────────────────────────────────────────

private def bool_and_split {a b : Bool} (h : a && b = true) :
    a = true ∧ b = true := by cases a <;> cases b <;> simp_all

private def bool_or_split {a b : Bool} (h : a || b = true) :
    a = true ∨ b = true := by cases a <;> cases b <;> simp_all

private def bool_and_join {a b : Bool} (ha : a = true) (hb : b = true) :
    a && b = true := by simp [ha, hb]

private def bool_or_join_left {a b : Bool} (ha : a = true) : a || b = true := by simp [ha]

private def bool_or_join_right {a b : Bool} (hb : b = true) : a || b = true := by simp [hb]

-- ─────────────────────────────────────────────────────────────────
-- Lemas de reducción
-- ─────────────────────────────────────────────────────────────────

theorem extEq_def (A B : CList) : extEq A B = (subset A B && subset B A) := by
  simp only [extEq, subset, evalOp]

theorem subset_nil (B : CList) : subset (mk []) B = true := by
  simp only [subset, evalOp]

theorem subset_cons (x : CList) (xs : List CList) (B : CList) :
    subset (mk (x :: xs)) B = (mem x B && subset (mk xs) B) := by
  simp only [subset, mem, evalOp]

theorem mem_nil (x : CList) : mem x (mk []) = false := by
  simp only [mem, evalOp]

theorem mem_cons (x y : CList) (ys : List CList) :
    mem x (mk (y :: ys)) = (extEq x y || mem x (mk ys)) := by
  simp only [mem, extEq, evalOp]

-- ─────────────────────────────────────────────────────────────────
-- Monotonicidad y reflexividad
-- ─────────────────────────────────────────────────────────────────

theorem subset_mono
    (xs : List CList) (y : CList) (ys : List CList)
    (h : evalOp .subset (mk xs) (mk ys) = true) :
    evalOp .subset (mk xs) (mk (y :: ys)) = true := by
  induction xs with
  | nil      => simp [evalOp]
  | cons z zs ih =>
    simp only [evalOp, Bool.and_eq_true] at h ⊢
    exact ⟨by simp [h.1], ih h.2⟩

theorem subset_refl (A : CList) : subset A A = true := by
  match A with
  | mk [] =>
    simp [subset, evalOp]
  | mk (x :: xs) =>
    have hx  : subset x x = true             := subset_refl x
    have hxs : subset (mk xs) (mk xs) = true := subset_refl (mk xs)
    simp only [subset] at hx hxs
    simp only [subset, evalOp, Bool.and_eq_true]
    exact ⟨by simp [hx], subset_mono xs x xs hxs⟩
termination_by (sizeOf A : Nat)
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

theorem extEq_refl (A : CList) : extEq A A = true := by
  simp only [extEq, evalOp, Bool.and_eq_true]
  exact ⟨subset_refl A, subset_refl A⟩

-- ─────────────────────────────────────────────────────────────────
-- Transitividad mutua
-- ─────────────────────────────────────────────────────────────────

mutual
  theorem extEq_trans :
      (A B C : CList) → (extEq A B = true) → (extEq B C = true) → (extEq A C = true)
    | A, B, C, h1, h2 => by
        simp only [extEq_def, Bool.and_eq_true] at h1 h2 ⊢
        exact ⟨subset_trans A B C h1.1 h2.1, subset_trans C B A h2.2 h1.2⟩
  termination_by A B C _ _ =>
    Nat.succ (Nat.mul (Nat.add (Nat.add (sizeOf A) (sizeOf B)) (sizeOf C)) 2)
  decreasing_by
    all_goals simp_wf
    all_goals try simp [sizeOf]
    all_goals try omega

  theorem subset_trans :
      (A B C : CList) → subset A B = true → subset B C = true → subset A C = true
    | mk [], _, _, _, _ => subset_nil _
    | mk (x :: xs), B, C, h1, h2 => by
        simp only [subset_cons, Bool.and_eq_true] at h1 ⊢
        exact ⟨mem_subset x B C h1.1 h2, subset_trans (mk xs) B C h1.2 h2⟩
  termination_by A B C _ _ =>
    Nat.mul (Nat.add (Nat.add (sizeOf A) (sizeOf B)) (sizeOf C)) 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [sizeOf]
    all_goals try omega

  theorem mem_subset :
      (x B C : CList) → mem x B = true → subset B C = true → mem x C = true
    | _, mk [], _, h1, _ => by simp [mem_nil] at h1
    | x, mk (y :: ys), C, h1, h2 => by
        simp only [mem_cons, Bool.or_eq_true] at h1
        simp only [subset_cons, Bool.and_eq_true] at h2
        cases h1 with
        | inl h1_eq  => exact mem_of_extEq x y C h1_eq h2.1
        | inr h1_mem => exact mem_subset x (mk ys) C h1_mem h2.2
  termination_by x B C _ _ =>
    Nat.mul (Nat.add (Nat.add (sizeOf x) (sizeOf B)) (sizeOf C)) 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [sizeOf]
    all_goals try omega

  theorem mem_of_extEq :
      (x y C : CList) → extEq x y = true → mem y C = true → mem x C = true
    | _, _, mk [], _, h2 => by simp [mem_nil] at h2
    | x, y, mk (z :: zs), h1, h2 => by
        simp only [mem_cons, Bool.or_eq_true] at h2 ⊢
        cases h2 with
        | inl h2_eq  => exact Or.inl (extEq_trans x y z h1 h2_eq)
        | inr h2_mem => exact Or.inr (mem_of_extEq x y (mk zs) h1 h2_mem)
  termination_by x y C _ _ =>
    Nat.mul (Nat.add (Nat.add (sizeOf x) (sizeOf y)) (sizeOf C)) 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [sizeOf]
    all_goals try omega
end

-- ─────────────────────────────────────────────────────────────────
-- Simetría
-- ─────────────────────────────────────────────────────────────────

theorem extEq_comm (A B : CList) : extEq A B = extEq B A := by
  simp [extEq_def, Bool.and_comm]

theorem extEq_symm {A B : CList} (h : extEq A B = true) : extEq B A = true := by
  rw [← extEq_comm]
  exact h

def Setoid : Setoid CList where
  r A B := extEq A B = true
  iseqv := {
    refl := extEq_refl
    symm := fun h => extEq_symm h
    trans := fun {A B C} h1 h2 => extEq_trans A B C h1 h2
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
-- =======

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
