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
def v123 : Vec Rat 3 :=
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

-- # 3. POLINOMIOS
--
-- En vez de funciones, que son abstractas, vamos a usar el tipo Poly
-- que modela polinomios como valores concretos.

def Vec.last {α : Type} : {n : Nat} → Vec α (n + 1) → α
  | 0,     Vec.cons x _  => x                   -- Caso base: vector de tamaño 1
  | _ + 1, Vec.cons _ xs => Vec.last xs         -- Caso recursivo: ignoramos la cabeza y buscamos en el resto

-- Ahora definimos la estructura:
structure FixPoly (grado : Nat) where
  -- 1. Los datos: un vector de racionales de tamaño (grado + 1)
  coefs : Vec Rat (grado + 1)

  -- 2. La propiedad: el último elemento del vector (el coef principal) NO es cero
  coef_principal_no_cero : coefs.last ≠ 0

-- El tipo Poly
inductive Poly where
| zero : Poly  -- El polinomio nulo: 0 [SIN GRADO Ó -INFINITY]
| const (c : Rat) (hneq0 : c ≠ 0) : Poly  -- Una constante: c [CON GRADO 0]
| mk (n : Nat) (p : FixPoly n) : Poly  -- Un polinomio: a₀ + a₁x + ... + aₙxⁿ [CON GRADO n]

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

-- 1. Evaluador auxiliar para un vector de coeficientes (Método de Horner)
def vecEval {m : Nat} (v : Vec Rat m) (x : Rat) : Rat :=
  match m, v with
  | 0,     Vec.nil       => 0
  | _ + 1, Vec.cons c cs => c + x * vecEval cs x
-- 2. El evaluador principal seguro por tipado
def polyEval (p : Poly) (x : Rat) : Rat :=
  match p with
  | Poly.zero      => 0
  | Poly.const c _ => c
  | Poly.mk _ fp   => vecEval fp.coefs x

-- # VERIFICACIÓN

-- 1. Primero construimos la estructura FixPoly (Grado 2)
def miPolinomioBase : FixPoly 2 := {
  coefs := Vec.cons (2 : Rat) (Vec.cons (3 : Rat) (Vec.cons (7 : Rat) Vec.nil)),
  -- Usamos 'by decide' para que Lean compruebe automáticamente que 7 ≠ 0
  coef_principal_no_cero := by decide
}
-- 2. Lo envolvemos en el tipo Poly general
def miPolinomio : Poly := Poly.mk 2 miPolinomioBase
-- 3. Evaluamos en x = 2
-- P(2) = 2 + 3(2) + 7(2²) = 2 + 6 + 28 = 36
#eval polyEval miPolinomio 2

-- Las variables que ya son polinomios (nulo y constante):
def coefs0 : Poly := Poly.zero
def coefs1 : Poly := Poly.const (1 : Rat) (by decide)
-- Tus vectores de coeficientes puros:
def coefs2 : Vec Rat 2 := Vec.cons 1 (Vec.cons 2 Vec.nil)
def coefs3 : Vec Rat 3 := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 Vec.nil))
def coefs4 : Vec Rat 4 := Vec.cons 1 (Vec.cons 2 (Vec.cons 3 (Vec.cons 4 Vec.nil)))
-- Para el cero y la constante, simplemente las renombramos (ya son Poly):
def poly0 : Poly := coefs0
def poly1 : Poly := coefs1
-- Para crear los polinomios de grado ≥ 1, primero empaquetamos
-- el vector en la estructura FixPoly junto con su prueba (by decide):
def base2 : FixPoly 1 := { coefs := coefs2, coef_principal_no_cero := by decide }
def poly2 : Poly := Poly.mk 1 base2
def base3 : FixPoly 2 := { coefs := coefs3, coef_principal_no_cero := by decide }
def poly3 : Poly := Poly.mk 2 base3
def base4 : FixPoly 3 := { coefs := coefs4, coef_principal_no_cero := by decide }
def poly4 : Poly := Poly.mk 3 base4
-- Y por último, evaluamos (recuerda que la nueva firma es: polyEval polinomio punto)
#eval polyEval poly0 (0 : Rat)
#eval polyEval poly1 1
#eval polyEval poly2 3   -- P(3) = 1 + 2(3) = 7
#eval polyEval poly3 2   -- P(2) = 1 + 2(2) + 3(2²) = 1 + 4 + 12 = 17-- # MAIN

def main : IO Unit := do
  IO.println "=== Sesión 3: Funciones de Tipos y Tipos Dependientes ==="
  IO.println s!"p(x) = 1+2x+3x²+4x³   en x=2  → {polyEval poly4 2}"
  IO.println s!"p(x) = 1+2x+3x²       en x=7  → {polyEval poly3 7}"
  IO.println s!"p(x) = 1+2x           en x=4  → {polyEval poly2 4}"
  IO.println s!"p(x) = 1              en x=9  → {polyEval poly1 9}"
  IO.println s!"p(x) = 0              en x=1  → {polyEval poly0 1}"
