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
