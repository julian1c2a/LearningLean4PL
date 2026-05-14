/-!
Sesión 2: Tipos Inductivos, Recursión y Option
-/

-- # 1. TIPOS INDUCTIVOS (inductive)
--
-- En Haskell usarías: data Color = Rojo | Verde | Azul
-- En Lean 4 es casi idéntico:

inductive Color where
  | rojo
  | verde
  | azul
  deriving BEq

-- Los constructores se acceden con Color.rojo, Color.verde, etc.
-- Aunque con `open` podemos omitir el prefijo:

open Color in
#eval toString (rojo == verde)  -- false

-- Pattern matching sobre un tipo inductivo:
def nombreColor (c : Color) : String :=
  match c with
  | Color.rojo  => "Rojo"
  | Color.verde => "Verde"
  | Color.azul  => "Azul"

#eval nombreColor Color.rojo   -- "Rojo"

-- # 2. TIPOS INDUCTIVOS CON DATOS
--
-- Equivalente a: data Forma = Circulo Float | Rectangulo Float Float

inductive Forma where
  | circulo    : Float → Forma
  | rectangulo : Float → Float → Forma

def area (f : Forma) : Float :=
  match f with
  | Forma.circulo r      => 3.14159265358979 * r * r
  | Forma.rectangulo a b => a * b

#eval area (Forma.circulo 3.0)        -- ≈ 28.27
#eval area (Forma.rectangulo 4.0 5.0) -- 20.0

-- # 3. TIPOS RECURSIVOS: LISTAS PROPIAS
--
-- Lean tiene List incorporado, pero construyámosla para entender la recursión.
-- Equivalente a: data MiLista a = Vacia | Cons a (MiLista a)

inductive MiLista (α : Type) where
  | vacia : MiLista α
  | cons  : α → MiLista α → MiLista α

-- Una lista de naturales: 1 :: 2 :: 3 :: []
def ejemplo : MiLista Nat :=
  MiLista.cons 1 (MiLista.cons 2 (MiLista.cons 3 MiLista.vacia))

-- Función recursiva: longitud de la lista
def longitud : MiLista α → Nat
  | MiLista.vacia      => 0
  | MiLista.cons _ xs  => 1 + longitud xs

#eval longitud ejemplo  -- 3

-- # 4. LA LISTA ESTÁNDAR DE LEAN 4
--
-- List α ya está definida. La notación [1, 2, 3] es azúcar sintáctico.

def lista1 : List Nat := [1, 2, 3, 4, 5]

-- Funciones básicas de listas (como en Haskell):
#eval lista1.length        -- 5
#eval lista1.head?         -- some 1  (nota el '?' — devuelve Option)
#eval lista1.tail          -- [2, 3, 4, 5]
#eval lista1.reverse       -- [5, 4, 3, 2, 1]
#eval lista1.map (· * 2)   -- [2, 4, 6, 8, 10]
#eval lista1.filter (· > 2) -- [3, 4, 5]
#eval lista1.foldl (· + ·) 0 -- 15

-- La notación (· * 2) es una lambda abreviada. Equivale a (fun x => x * 2)
-- Similar a las secciones de operadores en Haskell: (* 2)

-- # 5. EL TIPO Option
--
-- Equivalente al Maybe de Haskell: data Maybe a = Nothing | Just a
-- En Lean 4: Option α con constructores none y some

def dividir (a b : Float) : Option Float :=
  if b == 0.0 then none
  else some (a / b)

#eval dividir 10.0 2.0   -- some 5.0
#eval dividir 10.0 0.0   -- none

-- Pattern matching sobre Option:
def mostrarDivision (a b : Float) : String :=
  match dividir a b with
  | none   => "Error: división por cero"
  | some r => s!"{a} / {b} = {r}"

#eval mostrarDivision 10.0 2.0  -- "10.0 / 2.0 = 5.0"
#eval mostrarDivision 10.0 0.0  -- "Error: división por cero"

-- Option también tiene map y bind (como en Haskell):
#eval (some 5).map (· * 3)          -- some 15
#eval (none : Option Nat).map (· * 3) -- none

-- # 6. ESTRUCTURAS (structure)
--
-- Equivalente a los records de Haskell.
-- data Punto = Punto { x :: Float, y :: Float }

structure Punto where
  x : Float
  y : Float

def origen : Punto := { x := 0.0, y := 0.0 }
def p1 : Punto := { x := 3.0, y := 4.0 }

-- Acceso a campos con notación punto:
#eval p1.x  -- 3.0
#eval p1.y  -- 4.0

-- Distancia al origen:
def distancia (p : Punto) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval distancia p1  -- 5.0

-- Actualización de campos (record update syntax):
def p2 : Punto := { p1 with x := 0.0 }
#eval p2.x  -- 0.0
#eval p2.y  -- 4.0  (heredado de p1)

-- # MAIN: mostramos un resumen de la sesión

def main : IO Unit := do
  IO.println "=== Sesión 2: Tipos Inductivos, Recursión y Option ==="
  IO.println s!"Color: {nombreColor Color.azul}"
  IO.println s!"Área círculo r=3: {area (Forma.circulo 3.0)}"
  IO.println s!"Longitud [1,2,3]: {longitud ejemplo}"
  IO.println s!"Lista duplicada: {lista1.map (· * 2)}"
  IO.println s!"División 10/2:   {mostrarDivision 10.0 2.0}"
  IO.println s!"División 10/0:   {mostrarDivision 10.0 0.0}"
  IO.println s!"Distancia (3,4): {distancia p1}"
