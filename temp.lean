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

def OrdEquiv (α β : Ordinal) : Prop :=
  (α ≤ β) ∧ (β ≤ α)

axiom le_trans {α β γ : Ordinal} : α ≤ β → β ≤ γ → α ≤ γ

theorem ord_equiv_trans {α β γ : Ordinal} (h1 : OrdEquiv α β) (h2 : OrdEquiv β γ) : OrdEquiv α γ :=
  ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩

axiom ord_equiv_refl (α : Ordinal) : OrdEquiv α α
axiom ord_equiv_symm {α β : Ordinal} : OrdEquiv α β → OrdEquiv β α

instance ordSetoid : Setoid Ordinal where
  r := OrdEquiv
  iseqv := {
    refl := ord_equiv_refl
    symm := ord_equiv_symm
    trans := ord_equiv_trans
  }

def QOrdinal : Type 1 := Quotient ordSetoid

/- STREAMING_CHUNK: LIFT LE -/

theorem OrdLe_respects (a₁ a₂ b₁ b₂ : Ordinal) (h1 : a₁ ≈ a₂) (h2 : b₁ ≈ b₂) :
    (a₁ ≤ b₁) = (a₂ ≤ b₂) := by
  -- To prove equality of Props, we can use propext
  apply propext
  constructor
  · intro h
    -- h : a₁ ≤ b₁. We want a₂ ≤ b₂.
    -- h1.2 : a₂ ≤ a₁, h2.1 : b₁ ≤ b₂
    exact le_trans (le_trans h1.2 h) h2.1
  · intro h
    -- h : a₂ ≤ b₂. We want a₁ ≤ b₁.
    -- h1.1 : a₁ ≤ a₂, h2.2 : b₂ ≤ b₁
    exact le_trans (le_trans h1.1 h) h2.2

namespace QOrdinal

/-- Lift de OrdLe al cociente QOrdinal -/
def le (q₁ q₂ : QOrdinal) : Prop :=
  Quotient.lift₂ OrdLe OrdLe_respects q₁ q₂

instance : LE QOrdinal where
  le := le

end QOrdinal

