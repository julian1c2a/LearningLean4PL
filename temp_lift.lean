import learning_lean4_session_11

inductive Ordinal : Type 1
| zero : Ordinal
| succ : Ordinal → Ordinal
| sup : {α : Type} → (α → Ordinal) → Ordinal

inductive OrdLe : Ordinal → Ordinal → Prop where
| zero_le (b : Ordinal) : OrdLe Ordinal.zero b
| succ_le_succ {a b : Ordinal} : OrdLe a b → OrdLe (Ordinal.succ a) (Ordinal.succ b)
| le_sup {α : Type} {f : α → Ordinal} {b : Ordinal} (i : α) :
    OrdLe b (f i) → OrdLe b (Ordinal.sup f)
| sup_le {α : Type} {f : α → Ordinal} {b : Ordinal} :
    (∀ i, OrdLe (f i) b) → OrdLe (Ordinal.sup f) b

instance : LE Ordinal where le := OrdLe
def OrdLt (α β : Ordinal) : Prop := OrdLe (Ordinal.succ α) β
instance : LT Ordinal where lt := OrdLt

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

axiom le_trans {α β γ : Ordinal} : α ≤ β → β ≤ γ → α ≤ γ
def OrdEquiv (α β : Ordinal) : Prop := (α ≤ β) ∧ (β ≤ α)

axiom ord_equiv_refl (α : Ordinal) : OrdEquiv α α
axiom ord_equiv_symm {α β : Ordinal} : OrdEquiv α β → OrdEquiv β α
theorem ord_equiv_trans {α β γ : Ordinal} (h1 : OrdEquiv α β) (h2 : OrdEquiv β γ) : OrdEquiv α γ :=
  ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩

instance ordSetoid : Setoid Ordinal where
  r := OrdEquiv
  iseqv := { refl := ord_equiv_refl, symm := ord_equiv_symm, trans := ord_equiv_trans }

def QOrdinal : Type 1 := Quotient ordSetoid

namespace QOrdinal
def mk (a : Ordinal) : QOrdinal := Quotient.mk' a

/-- El ordinal 0 -/
def zero : QOrdinal := mk Ordinal.zero

/-- Demostramos que succ respeta la equivalencia -/
theorem succ_respects (a b : Ordinal) (h : a ≈ b) : Ordinal.succ a ≈ Ordinal.succ b := by
  constructor
  · exact OrdLe.succ_le_succ h.1
  · exact OrdLe.succ_le_succ h.2

/-- Lift de succ -/
def succ (q : QOrdinal) : QOrdinal :=
  Quotient.lift (fun a => mk (Ordinal.succ a)) (fun a b h => Quotient.sound (succ_respects a b h)) q

/-- Extraer un representante del cociente. -/
noncomputable def out (q : QOrdinal) : Ordinal :=
  Classical.choose (Quotient.exists_rep q)

/-- Lift de sup usando la extracción de representantes. -/
noncomputable def sup {α : Type} (f : α → QOrdinal) : QOrdinal :=
  mk (Ordinal.sup (fun i => out (f i)))

end QOrdinal
