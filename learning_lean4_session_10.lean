/- STREAMING_CHUNK: Configurando el entorno e importaciones simuladas -/

-- En un proyecto real, aquí usaríamos: import Jerarquia
-- Para que este archivo sea autoconteido, declaramos las estructuras que ya definiste:
axiom NextLevel (Base : Type u) : Type u
axiom NextLevel.pair : NextLevel Base → NextLevel Base → NextLevel Base
axiom NextLevel.union : NextLevel Base → NextLevel Base → NextLevel Base
axiom NextLevel.inter : NextLevel Base → NextLevel Base → NextLevel Base
axiom NextLevel.sUnion : NextLevel Base → NextLevel Base
axiom SetEquiv {Base : Type u} : NextLevel Base → NextLevel Base → Prop

/- STREAMING_CHUNK: Definiendo la relación de pertenencia (Mem) -/
/-- Definimos la pertenencia (∈) como una proposición inductiva.
    Esto le enseña a Lean las reglas lógicas de cuándo 'x' es un elemento de 'A'. -/
inductive Mem {Base : Type u} : NextLevel Base → NextLevel Base → Prop where
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
/-- Lean 4 utiliza la clase 'Membership' para habilitar el símbolo matemático '∈'.
    Le decimos que nuestra colección y nuestros elementos son del tipo NextLevel. -/
instance {Base : Type u} : Membership (NextLevel Base) (NextLevel Base) where
  mem x A := Mem x A

/- STREAMING_CHUNK: Conectando pertenencia con equivalencia (Extensionalidad) -/
/-- El puente final hacia Zermelo-Fraenkel: El Axioma de Extensionalidad.
    Dos conjuntos (árboles sintácticos) son equivalentes (≈) SI Y SOLO SI
    tienen exactamente los mismos elementos. -/
axiom extensionality {Base : Type u} (A B : NextLevel Base) :
  (∀ x : NextLevel Base, x ∈ A ↔ x ∈ B) ↔ (SetEquiv A B)
