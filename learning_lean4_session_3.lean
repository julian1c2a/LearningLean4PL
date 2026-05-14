/-!
Sesión 3: Funciones de Tipos y Tipos Dependientes
-/

-- # 1. TIPOS COMO VALORES DE PRIMERA CLASE
--
-- En Lean 4, Type es un ciudadano de primera clase: su propio tipo es Type 1.
-- Puedes escribir funciones que COMPUTAN tipos a partir de valores.
--
-- `def` vs `abbrev`: con `def` el elaborador no expande la definición al buscar
-- instancias de typeclasses (opaco). Con `abbrev` sí la expande (transparente).
-- Para funciones que computan tipos, usamos `abbrev`.

abbrev TipoSegunBool : Bool → Type
  | true  => Nat
  | false => String

def v1 : TipoSegunBool true  := 42      -- Lean reduce TipoSegunBool true → Nat
def v2 : TipoSegunBool false := "hola"  -- Lean reduce TipoSegunBool false → String

-- # 2. FunctNatType: TIPO DE FUNCIONES N-ARIAS SOBRE Nat
--
-- Equivalente Haskell (type family):
--   type family FunctNatType n where
--     FunctNatType 0       = Nat
--     FunctNatType (n + 1) = Nat -> FunctNatType n
--
-- Usamos `abbrev` para que el elaborador reduzca FunctNatType 0 a Nat,
-- FunctNatType 1 a Nat → Nat, etc., al resolver instancias y typechecks.

abbrev FunctNatType : Nat → Type
  | 0     => Nat
  | n + 1 => Nat → FunctNatType n

-- Verificamos las igualdades definitionales con rfl:
example : FunctNatType 0 = Nat               := rfl
example : FunctNatType 1 = (Nat → Nat)       := rfl
example : FunctNatType 2 = (Nat → Nat → Nat) := rfl

-- Ejemplos de valores de cada tipo:
def cte   : FunctNatType 0 := 42
def dobla : FunctNatType 1 := fun x => x * 2
def suma  : FunctNatType 2 := fun x y => x + y
def media : FunctNatType 3 := fun x y z => (x + y + z) / 3

#eval dobla 5        -- 10
#eval suma 3 4       -- 7
#eval media 3 6 9    -- 6

-- # 3. LISTAS DE LONGITUD FIJA (Vec)
--
-- Para garantizar en tiempo de compilación que pasamos EXACTAMENTE n argumentos
-- a una FunctNatType n, usamos un tipo indexado por longitud.
-- En Haskell: data Vec (n :: Nat) a
-- Clave: n es un ÍNDICE (varía por constructor), no un parámetro fijo.

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- El tipo garantiza la longitud: Vec Nat 3 tiene SIEMPRE 3 elementos.
def v123 : Vec Nat 3 :=
  Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))

-- Esto NO compila (longitud incorrecta — descomenta para ver el error):
-- def mal : Vec Nat 2 := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))

-- Aplicar una FunctNatType n a un Vec Nat n de exactamente n argumentos.
-- n queda como variable implícita auto-ligada desde los tipos de los argumentos.
def applyN : FunctNatType n → Vec Nat n → Nat
  | v, Vec.nil        => v
  | f, Vec.cons x xs  => applyN (f x) xs

#eval applyN suma  (Vec.cons 3 (Vec.cons 4 Vec.nil))                   -- 7
#eval applyN media (Vec.cons 3 (Vec.cons 6 (Vec.cons 9 Vec.nil)))      -- 6

-- # 4. EL EVALUADOR DE POLINOMIOS
--
-- Queremos:   polyEval pt n : FunctNatType n
-- que toma n coeficientes a₀, a₁, ..., aₙ₋₁ y evalúa en pt:
--   a₀ + a₁·pt + a₂·pt² + ... + aₙ₋₁·ptⁿ⁻¹
--
-- Problema: no podemos escribir directamente `(aₖ * acc) + FunctNatType n`
-- porque para n > 0 ese tipo es una función, no un Nat.
-- Solución: un auxiliar que inyecta una constante sumándola al resultado final.

def addToFunct : (n : Nat) → Nat → FunctNatType n → FunctNatType n
  | 0,     k, v => k + v                       -- base: sumar directamente al Nat
  | n + 1, k, f => fun x => addToFunct n k (f x)  -- rec: pasar a través de la función

-- Traza mental:
-- addToFunct 2 10 (fun a b => a + b)
--   = fun x => addToFunct 1 10 ((fun a b => a + b) x)
--   = fun x => fun y => addToFunct 0 10 (x + y)
--   = fun x y => 10 + x + y

-- El evaluador con acumulador de potencia (acc = pt^i para el término i-ésimo).
def polyEvalAux (pt acc : Nat) : (n : Nat) → FunctNatType n
  | 0     => 0
  | n + 1 => fun aₖ => addToFunct n (aₖ * acc) (polyEvalAux pt (acc * pt) n)

def polyEval (pt : Nat) (n : Nat) : FunctNatType n :=
  polyEvalAux pt 1 n

-- # VERIFICACIÓN

-- p(x) = 1 + 2x + 3x²  en  x=2:  1 + 4 + 12 = 17
#eval polyEval 2 3 1 2 3    -- 17

-- p(x) = 1 + x  en  x=7:  8
#eval polyEval 7 2 1 1      -- 8

-- p(x) = x²  en  x=4:  16
#eval polyEval 4 3 0 0 1    -- 16

-- p(x) = 3  (constante)  en  x=99:  3
#eval polyEval 99 1 3       -- 3

-- Combinando con applyN y Vec:
def coefs : Vec Nat 3 := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))
#eval applyN (polyEval 2 3) coefs   -- 17

-- # MAIN

def main : IO Unit := do
  IO.println "=== Sesión 3: Funciones de Tipos y Tipos Dependientes ==="
  IO.println s!"p(x) = 1+2x+3x²  en x=2  → {polyEval 2 3 1 2 3}"
  IO.println s!"p(x) = 1+x        en x=7  → {polyEval 7 2 1 1}"
  IO.println s!"p(x) = x²         en x=4  → {polyEval 4 3 0 0 1}"
  IO.println s!"p(x) = 3          en x=99 → {polyEval 99 1 3}"
