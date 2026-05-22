import os

content = """

/- STREAMING_CHUNK: LIFT LE -/

/-- Lema que demuestra que la relación ≤ respeta nuestra equivalencia. -/
theorem OrdLe_respects (a₁ a₂ b₁ b₂ : Ordinal) (h1 : a₁ ≈ a₂) (h2 : b₁ ≈ b₂) :
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
"""

with open("learning_lean4_session_12.lean", "a", encoding="utf-8") as f:
    f.write(content)
