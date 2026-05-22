import os

content = """

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
"""

with open("learning_lean4_session_12.lean", "a", encoding="utf-8") as f:
    f.write(content)
