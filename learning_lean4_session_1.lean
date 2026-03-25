/-!
Sesión 1: Introducción a Lean 4 como lenguage de programación
-/

-- Lean es un lenguaje de programación funcional con un sistema de tipos muy potente.
-- Dado que conoces Haskell, muchos conceptos te resultarán familiares.

-- # Definiciones y Tipos Básicos

-- Para definir una constante o una variable global, usamos `def`.
-- Lean puede inferir el tipo en muchos casos.
def miNombre := "Gemini"
def miEdad := 1

-- Pero es una buena práctica ser explícito con los tipos.
def unNumeroNatural : Nat := 5       -- Nat: Números naturales (0, 1, 2, ...)
def unEntero : Int := -10            -- Int: Números enteros (..., -1, 0, 1, ...)
def unBooleano : Bool := true        -- Bool: true o false
def unString : String := "Hola, Lean!"

-- `let` se usa para definiciones locales dentro de una función o bloque.
def saludoCompleto : String :=
  let saludo := "Hola"
  let objetivo := "mundo"
  s!"{saludo}, {objetivo}!" -- Esto es una cadena de texto interpolada, ¡muy útil!

-- `#check` es un comando para que Lean nos diga el tipo de una expresión.
-- En VS Code, puedes ver el resultado simplemente pasando el ratón por encima.
#check miNombre        -- Debería mostrar: String
#check unNumeroNatural  -- Debería mostrar: Nat
#check saludoCompleto   -- Debería mostrar: String

-- `#eval` es un comando para evaluar una expresión y ver su resultado.
#eval unNumeroNatural + 10
#eval saludoCompleto

-- # Funciones

-- La sintaxis de las funciones es similar a la de otros lenguajes funcionales.
-- def nombreFunción (argumento1 : Tipo1) (argumento2 : Tipo2) : TipoRetorno := cuerpo
def sumar (a : Nat) (b : Nat) : Nat :=
  a + b

-- Probemos la función
#eval sumar 5 3 -- Salida: 8

-- El `if/then/else` es una expresión, no una declaración. Siempre debe tener un `else`.
def esCero (n : Nat) : String :=
  if n == 0 then
    "Es cero"
  else
    "No es cero"

#eval esCero 0
#eval esCero 5

-- # El Mundo Real: IO y el punto de entrada `main`

-- Al igual que en Haskell, las acciones con "efectos secundarios" (como imprimir en
-- la consola) se gestionan dentro de un contexto especial: el mónada `IO`.
-- Por ahora, piénsalo como una "etiqueta" para funciones que "hacen algo" en el mundo exterior.
-- Una función que devuelve `IO Unit` es una acción que no produce un valor de retorno
-- significativo (similar a `void` en C++ o `IO ()` en Haskell).

-- La función `main` es el punto de entrada de cualquier programa ejecutable en Lean.
def main : IO Unit :=
  IO.println s!"Hola, {miNombre}. ¡Empecemos a aprender Lean!"

-- Para compilar y ejecutar este programa:
-- 1. Abre una terminal en la raíz de tu proyecto.
-- 2. Ejecuta `lake build`.
-- 3. Ejecuta el binario: `.lake\build\bin\learninglean4.exe` (en Windows)
-- 3. Ejecuta el binario con `lake run` o directamente: `.\build\bin\learninglean4.exe` (en Windows)
