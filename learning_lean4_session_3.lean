import Lean.ToExpr
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

-- Inyecta un coeficiente c al inicio de un polinomio p
def Poly.cons (c : Rat) (p : Poly) : Poly :=
  match p with
  | Poly.zero =>
    -- Si hasta ahora todo era cero, miramos el nuevo coeficiente c.
    -- Si c también es cero, el polinomio sigue siendo nulo (¡así ignoramos los ceros finales!).
    if h : c = 0 then
      Poly.zero
    else
      Poly.const c h
  | Poly.const k hk =>
    -- Si teníamos una constante k (que sabemos que es ≠ 0), al añadir c
    -- pasamos a tener grado 1: c + kx
    let v := Vec.cons c (Vec.cons k Vec.nil)
    Poly.mk 1 {
      coefs := v,
      coef_principal_no_cero := hk
    }
  | Poly.mk n fp =>
    -- Si ya teníamos un polinomio de grado n ≥ 1, simplemente
    -- añadimos el nuevo coeficiente al principio del vector.
    let v := Vec.cons c fp.coefs
    -- ¡La magia de Lean! Como hemos añadido el elemento al PRINCIPIO del vector,
    -- el ÚLTIMO elemento sigue siendo exactamente el mismo.
    -- Por lo tanto, ¡nuestra prueba matemática fp.coef_principal_no_cero sigue siendo 100% válida!
    Poly.mk (n + 1) {
      coefs := v,
      coef_principal_no_cero := fp.coef_principal_no_cero
    }

-- Ahora construir el polinomio descartando los ceros del final se hace en una sola línea
-- usando `foldr` (que procesa la lista de derecha a izquierda).
def Poly.fromList (L : List Rat) : Poly :=
  L.foldr Poly.cons Poly.zero


-- # VERIFICACIÓN

-- 1. Primero construimos la estructura FixPoly (Grado 2)
def miPolinomioBase : Poly := Poly.fromList [2, 3, 7]
-- 2. Lo envolvemos en el tipo Poly general
def miPolinomio : Poly := Poly.cons 1 miPolinomioBase
-- 3. Evaluamos en x = 2
-- P(2) = 2 + 3(2) + 7(2²) = 2 + 6 + 28 = 36
#eval polyEval miPolinomio 2

-- Las variables que ya son polinomios (nulo y constante):
def poly0 : Poly := Poly.fromList []
def poly1 : Poly := Poly.fromList [1]
-- Tus vectores de coeficientes puros:
def poly2 : Poly := Poly.fromList [1, 2]
def poly3 : Poly := Poly.fromList [1, 2, 3]
def poly4 : Poly := Poly.fromList [1, 2, 3, 4]
def poly5 : Poly := Poly.fromList [1, 2, 3, 4, 5]

#eval polyEval poly0 (0 : Rat)
#eval polyEval poly1 1
#eval polyEval poly2 3   -- P(3) = 1 + 2(3) = 7
#eval polyEval poly3 2   -- P(2) = 1 + 2(2) + 3(2²) = 1 + 4 + 12 = 17-- # MAIN

def main : IO Unit := do
  IO.println "=== Sesión 3: Funciones de Tipos y Tipos Dependientes ==="
  IO.println s!"p(x) = 1+2x+3x²+4x³+5x⁴   en x=9  → {polyEval poly5 9}"
  IO.println s!"p(x) = 1+2x+3x²+4x³       en x=2  → {polyEval poly4 2}"
  IO.println s!"p(x) = 1+2x+3x²           en x=7  → {polyEval poly3 7}"
  IO.println s!"p(x) = 1+2x               en x=4  → {polyEval poly2 4}"
  IO.println s!"p(x) = 1                  en x=9  → {polyEval poly1 9}"
  IO.println s!"p(x) = 0                  en x=1  → {polyEval poly0 1}"
