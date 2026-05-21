import learning_lean4_session_10

/-!
Sesión 11: Ordinales de Brouwer y el Universo Transfinito
=========================================================
En esta sesión abandonamos `Nat` como índice de nuestra jerarquía de
universos y pasamos a los Ordinales (`Ordinal`). Esto nos permite alcanzar
V_ω, V_{ω+ω}, y límites arbitrarios (Cardinales Inaccesibles) gracias
al constructor `sup`.
-/

/- STREAMING_CHUNK: Los Ordinales (Árboles de Brouwer) -/
/-- Un ordinal constructivo. El constructor `sup` toma una secuencia indexada
    por CUALQUIER tipo `α`, permitiendo límites numerables y no numerables. -/
inductive Ordinal : Type 1 where
| zero : Ordinal
| succ : Ordinal → Ordinal
| sup  {α : Type} : (α → Ordinal) → Ordinal

/- STREAMING_CHUNK: Andamiaje del Súper-Colímite Transfinito -/
/-- Representa el Súper-Colímite: La unión disjunta de todos los niveles generados por `f`. -/
def V_PreLimit {α : Type} (f : α → Type) : Type :=
  Σ (a : α), f a

/-- Axioma: Existe una relación de equivalencia que colapsa el Pre-Límite pegando 
    los conjuntos que son extensiones el uno del otro a lo largo de la secuencia. -/
axiom limitEquiv {α : Type} (f : α → Type) : V_PreLimit f → V_PreLimit f → Prop

/-- El Setoid sobre el límite que permite crear el cociente. -/
instance limitSetoid {α : Type} (f : α → Type) : Setoid (V_PreLimit f) where
  r := limitEquiv f
  iseqv := sorry -- Requiere una prueba compleja de inducción-recursión

/- STREAMING_CHUNK: El Universo Transfinito (V) -/
/-- 
Para evitar la barrera de definición Inductivo-Recursiva de Lean 4 
(donde el tipo depende de la Pertenencia, y la Pertenencia depende del tipo), 
declaramos el universo V matemáticamente usando axiomas estructurales. 
-/
axiom V : Ordinal → Type

-- Aseguramos que todo nivel de V tenga una noción de pertenencia
axiom V_mem (o : Ordinal) : Membership (V o) (V o)
attribute [instance] V_mem

-- Las tres ecuaciones de ZFC para la Jerarquía Acumulativa:
-- 1. Nivel cero es HFSet (V_ω)
axiom V_zero : V Ordinal.zero = HFSet

-- 2. El nivel sucesor es el conjunto potencia (QNextLevel) del anterior
axiom V_succ (α : Ordinal) : V (Ordinal.succ α) = QNextLevel (V α)

-- 3. El nivel límite es el colímite (Quotient) de todos los niveles anteriores
axiom V_sup {α : Type} (f : α → Ordinal) : 
  V (Ordinal.sup f) = Quotient (limitSetoid (fun a => V (f a)))

/-- Ejemplo de notación: Omega es el límite sobre los números naturales. -/
def omega : Ordinal := Ordinal.sup (fun n : Nat => 
  -- Una secuencia simple: 0, 1, 2...
  let rec f : Nat → Ordinal
  | 0 => Ordinal.zero
  | n + 1 => Ordinal.succ (f n)
  f n
)

-- El universo V_omega+omega ya es un objeto de primera clase:
#check V (Ordinal.succ omega)
