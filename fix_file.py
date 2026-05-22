import os

with open("learning_lean4_session_12.lean", "r", encoding="utf-8") as f:
    lines = f.readlines()

output_lines = []
for line in lines:
    if line.startswith("/- STREAMING_CHUNK: CONSTRUCTORES QORDINAL -/"):
        break
    output_lines.append(line)

content = """/- STREAMING_CHUNK: CONSTRUCTORES QORDINAL -/

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
"""

with open("learning_lean4_session_12.lean", "w", encoding="utf-8") as f:
    f.writelines(output_lines)
    f.write(content)
