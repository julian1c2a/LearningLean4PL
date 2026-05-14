/-!
Sesión 4: Typeclasses
-/

-- # 1. QUÉ ES UNA TYPECLASS
--
-- Una typeclass define una interfaz que los tipos pueden implementar.
-- En Haskell: class Describible a where describir :: a -> String
-- En Lean 4:

class Describible (α : Type) where
  describir : α → String

instance : Describible Nat where
  describir n := s!"el natural {n}"

instance : Describible Bool where
  describir b := if b then "verdadero" else "falso"

#eval Describible.describir (42 : Nat)  -- "el natural 42"
#eval Describible.describir true        -- "verdadero"

-- # 2. TYPECLASSES ESTÁNDAR
--
-- ToString : usado en s!"...{x}..."
-- Repr     : usado en #eval para mostrar valores
-- BEq      : igualdad booleana (==)
-- Inhabited: tipo que tiene un valor por defecto

inductive Color where
  | rojo | verde | azul
  deriving BEq, Repr   -- Repr muestra nombres de constructores; BEq da ==

#eval Color.rojo                  -- Color.rojo
#eval Color.rojo == Color.verde   -- false

-- ToString personalizado para interpolación en strings:
instance : ToString Color where
  toString
    | Color.rojo  => "Rojo"
    | Color.verde => "Verde"
    | Color.azul  => "Azul"

#eval s!"Color favorito: {Color.azul}"  -- "Color favorito: Azul"

-- Inhabited: valor por defecto del tipo
instance : Inhabited Color where
  default := Color.rojo

#eval (default : Color)  -- Color.rojo

-- # 3. DERIVING: atajo para instancias mecánicas

inductive Forma where
  | circulo    : Float → Forma
  | rectangulo : Float → Float → Forma
  deriving BEq, Repr

#eval Forma.circulo 3.0                               -- Forma.circulo 3.000000
#eval Forma.circulo 3.0 == Forma.rectangulo 3.0 4.0   -- false

-- # 4. TYPECLASS CON MÚLTIPLES MÉTODOS

class Contenedor (f : Type → Type) where
  vacio   : f α
  tamano  : f α → Nat
  agregar : α → f α → f α

instance : Contenedor List where
  vacio        := []
  tamano       := List.length
  agregar x xs := x :: xs

-- Función genérica que funciona con cualquier Contenedor:
-- [Contenedor f] es el argumento de typeclass implícito (como (Contenedor f) => en Haskell)
def llenar [Contenedor f] (xs : List α) : f α :=
  xs.foldr Contenedor.agregar Contenedor.vacio

#eval (llenar [1, 2, 3] : List Nat)  -- [1, 2, 3]

-- # 5. INSTANCIAS PARA TIPOS PARAMÉTRICOS
--
-- En Haskell: instance Show a => Show (Maybe a) where ...
-- En Lean 4:  instance [ToString α] : ToString (Option α) where ...

instance [ToString α] : ToString (Option α) where
  toString
    | none   => "ninguno"
    | some x => s!"some({x})"

#eval s!"{(some 42 : Option Nat)}"  -- "some(42)"
#eval s!"{(none : Option Nat)}"     -- "ninguno"

-- # 6. INSTANCIAS PARA TIPOS DEPENDIENTES: Vec
--
-- Con let rec el tipo implícito m no se auto-liga bien;
-- es más limpio definir helpers privados con def.

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

private def vecToString [ToString α] : Vec α n → String
  | Vec.nil            => ""
  | Vec.cons x Vec.nil => toString x
  | Vec.cons x xs      => toString x ++ ", " ++ vecToString xs

instance [ToString α] : ToString (Vec α n) where
  toString v := "[" ++ vecToString v ++ "]"

private def vecBeq [BEq α] : Vec α n → Vec α n → Bool
  | Vec.nil,       Vec.nil       => true
  | Vec.cons x xs, Vec.cons y ys => x == y && vecBeq xs ys

instance [BEq α] : BEq (Vec α n) where
  beq := vecBeq

def vEj : Vec Nat 3 := Vec.cons 10 (Vec.cons 20 (Vec.cons 30 Vec.nil))
def v1  : Vec Nat 2 := Vec.cons 1 (Vec.cons 2 Vec.nil)
def v2  : Vec Nat 2 := Vec.cons 1 (Vec.cons 9 Vec.nil)

#eval s!"{vEj}"   -- "[10, 20, 30]"
#eval v1 == v1    -- true
#eval v1 == v2    -- false

-- # 7. SUPERCLASES con `extends`
--
-- En Haskell: class Eq a => Ord a where ...
-- En Lean 4 se usa `extends`:

class Ordenable (α : Type) extends BEq α where
  menor : α → α → Bool

-- La instancia debe proveer tanto `beq` (de BEq) como `menor` (de Ordenable):
instance : Ordenable Nat where
  beq   a b := a == b
  menor a b := a < b

-- Con `extends`, tener Ordenable implica tener BEq automáticamente:
def minimoLista [Ordenable α] [Inhabited α] : List α → α
  | []      => default
  | [x]     => x
  | x :: xs =>
      let m := minimoLista xs
      if Ordenable.menor x m then x else m

#eval minimoLista ([] : List Nat)       -- 0  (default de Nat)
#eval minimoLista [5, 3, 8, 1, 4]      -- 1

-- # MAIN

def main : IO Unit := do
  IO.println "=== Sesión 4: Typeclasses ==="
  IO.println s!"Describible Nat:  {Describible.describir (10 : Nat)}"
  IO.println s!"Describible Bool: {Describible.describir false}"
  IO.println s!"Color:   {Color.verde}"
  IO.println s!"Option:  {(some 42 : Option Nat)}"
  IO.println s!"Vec:     {vEj}"
  IO.println s!"v1==v1:  {v1 == v1},  v1==v2: {v1 == v2}"
  IO.println s!"mínimo [5,3,8,1,4]: {minimoLista [5, 3, 8, 1, 4]}"
