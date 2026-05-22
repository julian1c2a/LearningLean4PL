import os

content = """

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
"""

with open("learning_lean4_session_12.lean", "a", encoding="utf-8") as f:
    f.write(content)
