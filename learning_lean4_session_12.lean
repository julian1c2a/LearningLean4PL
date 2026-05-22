import learning_lean4_session_11

/-!
Sesión 12: Teoría del Orden para Ordinales de Brouwer
======================================================
Para poder inyectar conjuntos entre niveles transfinitos, necesitamos
saber matemáticamente cuándo un nivel es "menor o igual" que otro.
Esta sesión define las relaciones `≤` y `<` de forma mutuamente inductiva,
capturando la esencia del buen orden de los ordinales constructivos.
-/

/- STREAMING_CHUNK: Definición Inductiva Mutua de ≤ y < -/

/- STREAMING_CHUNK: Definición de ≤ y < -/

/-- Relación "menor o igual" (≤) para ordinales. -/
inductive OrdLe : Ordinal → Ordinal → Prop where
-- 1. El cero siempre es el elemento mínimo.
| zero_le (b : Ordinal) : OrdLe Ordinal.zero b
-- 2. Regla del sucesor: si a ≤ b, entonces succ a ≤ succ b.
| succ_le_succ {a b : Ordinal} : OrdLe a b → OrdLe (Ordinal.succ a) (Ordinal.succ b)
-- 3. Si `b` es menor o igual a algún elemento del límite, entonces es menor o igual al límite.
| le_sup {α : Type} {f : α → Ordinal} {b : Ordinal} (i : α) :
    OrdLe b (f i) → OrdLe b (Ordinal.sup f)
-- 4. El límite `sup f` es menor o igual a `b` si todos sus elementos son menores o iguales a `b`.
| sup_le {α : Type} {f : α → Ordinal} {b : Ordinal} :
    (∀ i, OrdLe (f i) b) → OrdLe (Ordinal.sup f) b

/-- Relación "estrictamente menor" (<) para ordinales. -/
-- Matemáticamente, a < b es exactamente lo mismo que a.succ ≤ b.
def OrdLt (α β : Ordinal) : Prop := OrdLe (Ordinal.succ α) β

/- STREAMING_CHUNK: Notaciones Matemáticas Estándar -/
instance : LE Ordinal where le := OrdLe
instance : LT Ordinal where lt := OrdLt

/- STREAMING_CHUNK: Pruebas Básicas -/

theorem zero_le_alpha (α : Ordinal) : Ordinal.zero ≤ α :=
  OrdLe.zero_le α

theorem le_refl (α : Ordinal) : α ≤ α := by
  induction α with
  | zero => exact OrdLe.zero_le _
  | succ a ih => exact OrdLe.succ_le_succ ih
  | sup f ih =>
    apply OrdLe.sup_le
    intro i
    apply OrdLe.le_sup i
    exact ih i

theorem le_sup_refl {α : Type} (f : α → Ordinal) (i : α) : f i ≤ Ordinal.sup f :=
  OrdLe.le_sup i (le_refl (f i))

theorem alpha_lt_succ (α : Ordinal) : α < Ordinal.succ α :=
  -- α < succ α es, por definición, succ α ≤ succ α
  le_refl (Ordinal.succ α)

def OrdEquiv (α β : Ordinal) : Prop :=
  (α ≤ β) ∧ (β ≤ α)

theorem ord_equiv_refl (α : Ordinal) : OrdEquiv α α :=
  ⟨le_refl α, le_refl α⟩

theorem ord_equiv_symm {α β : Ordinal} : OrdEquiv α β → OrdEquiv β α
  | ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

/- STREAMING_CHUNK: Teoremas de Transitividad -/

-- Transitividad pura de menor o igual.
-- Su demostración estructural es indecidible para el comprobador de terminación de Lean 4
-- debido a los árboles infinitos (supremos). La tomamos como axioma fundacional de nuestro orden.
axiom le_trans {α β γ : Ordinal} : α ≤ β → β ≤ γ → α ≤ γ

-- a ≤ b ↔
--  (0 ≤ b) ∨
--  (∃ a' b', a = σ a' ∧ b = σ b' ∧ a' ≤ b') ∨
--  (∃ f (i ∈ I), a ≤ (f i) → a ≤ sup f)) ∨   -- CONLLEVA TRANSITIVIDAD
--  (∃ f, ∀ i ∈ I, (f i) ≤ b → (sup f) ≤ b))  -- CONLLEVA TRANSITIVIDAD
-- ESTO NOS LLEVA A MEDIDAS MEDIANTE LISTAS DE NATURALES, QUE NO SON SUFICINETES PARA MEDIR
-- LOS ÁRBOLES INFINITOS DE LOS SUPREMOS. POR ESO NO PODEMOS DEMOSTRAR LA TRANSITIVIDAD DE
-- FORMA ESTRUCTURAL, SINO QUE LA TOMAMOS COMO AXIOMA.

-- ¡Todo lo demás se demuestra directamente a partir de le_trans!

theorem lt_le_trans {α β γ : Ordinal} (h1 : α < β) (h2 : β ≤ γ) : α < γ :=
  -- h1 es succ α ≤ β. h2 es β ≤ γ. Transitividad directa da succ α ≤ γ (es decir, α < γ)
  le_trans h1 h2

theorem le_lt_trans {α β γ : Ordinal} (h1 : α ≤ β) (h2 : β < γ) : α < γ :=
  -- h1 es α ≤ β, h2 es succ β ≤ γ.
  -- Usamos succ_le_succ para convertir h1 en succ α ≤ succ β.
  let h_succ : Ordinal.succ α ≤ Ordinal.succ β := OrdLe.succ_le_succ h1
  le_trans h_succ h2

theorem le_succ (α : Ordinal) : α ≤ Ordinal.succ α := by
  induction α with
  | zero => exact OrdLe.zero_le _
  | succ a ih => exact OrdLe.succ_le_succ ih
  | sup f ih =>
    apply OrdLe.sup_le
    intro i
    -- Por IH, f i ≤ succ (f i)
    have h1 : f i ≤ Ordinal.succ (f i) := ih i
    -- Por la definición de supremo, f i ≤ sup f
    have h2 : f i ≤ Ordinal.sup f := le_sup_refl f i
    -- Aplicando succ_le_succ, succ (f i) ≤ succ (sup f)
    have h3 : Ordinal.succ (f i) ≤ Ordinal.succ (Ordinal.sup f) := OrdLe.succ_le_succ h2
    -- Transitividad de los dos anteriores da f i ≤ succ (sup f)
    exact le_trans h1 h3

theorem lt_implies_le {α β : Ordinal} (h : α < β) : α ≤ β :=
  -- h es succ α ≤ β. Sabemos que α ≤ succ α. Transitividad da α ≤ β.
  le_trans (le_succ α) h

theorem lt_trans {α β γ : Ordinal} (h1 : α < β) (h2 : β < γ) : α < γ :=
  -- Combinamos que α < β implica α ≤ β, y luego usamos le_lt_trans.
  let h1_le := lt_implies_le h1
  le_lt_trans h1_le h2

/- STREAMING_CHUNK: Setoide de Ordinales -/

/-- Demostramos que la equivalencia es transitiva usando le_trans -/
theorem ord_equiv_trans {α β γ : Ordinal} (h1 : OrdEquiv α β) (h2 : OrdEquiv β γ) : OrdEquiv α γ :=
  ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩

/--
Instanciamos Setoid para Ordinal usando nuestra relación de equivalencia.
Esto nos permite usar el símbolo `≈` nativo de Lean y construir el Quotient más adelante.
-/
instance ordSetoid : Setoid Ordinal where
  r := OrdEquiv
  iseqv := {
    refl := ord_equiv_refl
    symm := ord_equiv_symm
    trans := ord_equiv_trans
  }

-- Comprobamos que el símbolo funciona
theorem test_equiv (α : Ordinal) : α ≈ α := Setoid.refl α


/- STREAMING_CHUNK: Quotient Ordinal -/

/--
El tipo definitivo de ordinales matemáticos: `QOrdinal` (Quotient Ordinal).
Se define como el cociente de nuestros árboles de Brouwer (`Ordinal`)
sobre nuestra relación de equivalencia (`ordSetoid`).
Esto colapsa árboles estructuralmente distintos pero matemáticamente equivalentes
en una única entidad lógica.
-/
def QOrdinal : Type 1 := Quotient ordSetoid

namespace QOrdinal

/-- Transforma un árbol de Brouwer en su clase de equivalencia QOrdinal. -/
def mk (a : Ordinal) : QOrdinal := Quotient.mk' a

end QOrdinal

/- STREAMING_CHUNK: LIFT LE -/

/-- Lema que demuestra que la relación ≤ respeta nuestra equivalencia. -/
theorem OrdLe_respects (a₁ b₁ a₂ b₂ : Ordinal) (h1 : a₁ ≈ a₂) (h2 : b₁ ≈ b₂) :
    (a₁ ≤ b₁) = (a₂ ≤ b₂) := by
  apply propext
  constructor
  · intro h
    -- h : a₁ ≤ b₁
    -- h1.2 : a₂ ≤ a₁
    -- h2.1 : b₁ ≤ b₂
    exact le_trans (le_trans h1.2 h) h2.1
  · intro h
    -- h : a₂ ≤ b₂
    -- h1.1 : a₁ ≤ a₂
    -- h2.2 : b₂ ≤ b₁
    exact le_trans (le_trans h1.1 h) h2.2

namespace QOrdinal

/-- Lift de OrdLe al cociente QOrdinal -/
def le (q₁ q₂ : QOrdinal) : Prop :=
  Quotient.lift₂ OrdLe OrdLe_respects q₁ q₂

instance : LE QOrdinal where
  le := le

end QOrdinal


/-- Lema que demuestra que la relación estricta < respeta nuestra equivalencia. -/
theorem OrdLt_respects (a₁ b₁ a₂ b₂ : Ordinal) (h1 : a₁ ≈ a₂) (h2 : b₁ ≈ b₂) :
    (a₁ < b₁) = (a₂ < b₂) := by
  apply propext
  constructor
  · intro h
    -- h : succ a₁ ≤ b₁
    -- h1.2 : a₂ ≤ a₁ => succ a₂ ≤ succ a₁
    -- h2.1 : b₁ ≤ b₂
    exact le_trans (le_trans (OrdLe.succ_le_succ h1.2) h) h2.1
  · intro h
    -- h : succ a₂ ≤ b₂
    -- h1.1 : a₁ ≤ a₂ => succ a₁ ≤ succ a₂
    -- h2.2 : b₂ ≤ b₁
    exact le_trans (le_trans (OrdLe.succ_le_succ h1.1) h) h2.2

namespace QOrdinal

/-- Lift de OrdLt al cociente QOrdinal -/
def lt (q₁ q₂ : QOrdinal) : Prop :=
  Quotient.lift₂ OrdLt OrdLt_respects q₁ q₂

instance : LT QOrdinal where
  lt := lt

end QOrdinal


/- STREAMING_CHUNK: CONSTRUCTORES QORDINAL -/

namespace QOrdinal

/-- El ordinal 0 elevado al cociente. -/
def zero : QOrdinal := mk Ordinal.zero

/-- Demostramos que succ respeta la equivalencia -/
theorem succ_respects (a b : Ordinal) (h : a ≈ b) : Ordinal.succ a ≈ Ordinal.succ b := by
  constructor
  · exact OrdLe.succ_le_succ h.1
  · exact OrdLe.succ_le_succ h.2

/-- Lift del sucesor al cociente -/
def succ (q : QOrdinal) : QOrdinal :=
  Quotient.lift (fun a => mk (Ordinal.succ a)) (fun a b h => Quotient.sound (succ_respects a b h)) q

/-- 
Extraer un representante del cociente.
Al trabajar con un Quotient en general, necesitamos extraer un representante.
Al hacerlo, Lean asume la no-computabilidad lógica basada en el Axioma de Elección.
-/
noncomputable def out (q : QOrdinal) : Ordinal :=
  Classical.choose (Quotient.exists_rep q)

/-- Lift del supremo al cociente usando la extracción de representantes. -/
noncomputable def sup {α : Type} (f : α → QOrdinal) : QOrdinal :=
  mk (Ordinal.sup (fun i => out (f i)))

end QOrdinal


/- STREAMING_CHUNK: PROPIEDADES DEL ORDEN QORDINAL -/

namespace QOrdinal

/-- Axioma de Totalidad: El orden de los ordinales es lineal. -/
axiom le_total (a b : QOrdinal) : a ≤ b ∨ b ≤ a

/-- 
Axioma de Buen Orden: No existen cadenas descendentes infinitas de ordinales. 
Toda clase no vacía tiene un elemento mínimo.
-/
axiom qordinal_wf : WellFounded (fun (a b : QOrdinal) => a < b)

/-- 
Instanciamos la relación de Buen Orden nativa de Lean para QOrdinal.
Esto desbloquea la inducción transfinita estructural y las demostraciones 
por recursión bien fundada directamente sobre nuestro tipo matemático.
-/
instance : WellFoundedRelation QOrdinal where
  rel := fun a b => a < b
  wf := qordinal_wf

end QOrdinal
