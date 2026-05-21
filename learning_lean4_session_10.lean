/- STREAMING_CHUNK: Configurando el entorno e importaciones simuladas -/

import learning_lean4_session_9

/- STREAMING_CHUNK: Definiendo la relación de pertenencia (Mem) -/
/-- Definimos la pertenencia (∈) como una proposición inductiva.
    Esto le enseña a Lean las reglas lógicas de cuándo 'x' es un elemento de 'A'. -/
inductive Mem {Base : Type u} [Membership Base Base] : NextLevel Base → NextLevel Base → Prop where
-- 0. Puente entre universos
| in_inj {x y : Base} : (x ∈ y) → Mem (NextLevel.inj x) (NextLevel.inj y)
-- 1. Pertenencia en el Par: x ∈ {A, B} si x es estructuralmente A, o x es B
| in_pair_left (A B : NextLevel Base) : Mem A (NextLevel.pair A B)
| in_pair_right (A B : NextLevel Base) : Mem B (NextLevel.pair A B)
-- 2. Pertenencia en la Unión Binaria: x ∈ A U B si x ∈ A o x ∈ B
| in_union_left {x A B : NextLevel Base} : Mem x A → Mem x (NextLevel.union A B)
| in_union_right {x A B : NextLevel Base} : Mem x B → Mem x (NextLevel.union A B)
-- 3. Pertenencia en la Intersección: x ∈ A ∩ B requiere que esté en ambos
| in_inter {x A B : NextLevel Base} : Mem x A → Mem x B → Mem x (NextLevel.inter A B)
-- 4. Pertenencia en la Gran Unión: x ∈ ⋃A si existe algún conjunto Y ∈ A tal que x ∈ Y
| in_sUnion {x Y A : NextLevel Base} : Mem Y A → Mem x Y → Mem x (NextLevel.sUnion A)

/- STREAMING_CHUNK: Configurando la notación estándar de pertenencia (∈) -/
instance {Base : Type u} [Membership Base Base] : Membership (NextLevel Base) (NextLevel Base) where
  mem x A := Mem x A

/- STREAMING_CHUNK: Equivalencia Extensional -/
/-- Definición pura de equivalencia: Dos conjuntos son equivalentes si tienen los mismos elementos. -/
def SetEquiv {Base : Type u} [Membership Base Base] (A B : NextLevel Base) : Prop :=
  ∀ x : NextLevel Base, x ∈ A ↔ x ∈ B

-- ==========================================
-- EL COCIENTE (El Verdadero Universo Matemático)
-- ==========================================
-- Registramos la instancia oficial de Setoid en Lean
instance nextLevelSetoid {Base : Type u} [Membership Base Base] : Setoid (NextLevel Base) where
  r := SetEquiv
  iseqv := {
    refl  := fun _ _ => Iff.rfl
    symm  := fun h x => Iff.symm (h x)
    trans := fun h1 h2 x => Iff.trans (h1 x) (h2 x)
  }

-- QNextLevel (Quotient Next Level) colapsa todos los árboles equivalentes.
def QNextLevel (Base : Type u) [Membership Base Base] : Type u := Quotient (@nextLevelSetoid Base _)
