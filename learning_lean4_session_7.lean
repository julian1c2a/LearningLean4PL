/-!
Sesión 7: HFSet — Conjuntos Finitos Hereditarios (universo de Aczel finito)

Convención de argumentos en toda la sesión:
  - El SET siempre es el primer argumento (receptor del dot notation)
  - El ELEMENTO es el segundo argumento
  Ejemplo: s.insert x = "insertar x en s"
           s.mem    x = "¿está x en s?"
-/

-- ================================================================
-- 1. EL TIPO
-- ================================================================
-- Representación: lista ORDENADA y SIN DUPLICADOS de HFSets.
-- Invariante mantenida por los smart constructors.

inductive HFSet : Type where
  | node : List HFSet → HFSet

-- ================================================================
-- 2. COMPARACIÓN (bien fundada por inducción estructural)
-- ================================================================

def HFSet.cmp : HFSet → HFSet → Ordering
    | HFSet.node [],        HFSet.node []        => .eq
    | HFSet.node [],        HFSet.node (_ :: _)  => .lt
    | HFSet.node (_ :: _),  HFSet.node []        => .gt
    | HFSet.node (x :: xs), HFSet.node (y :: ys) =>
      match HFSet.cmp x y with
      | .eq => HFSet.cmp (HFSet.node xs) (HFSet.node ys)
      | o   => o
termination_by a b => sizeOf a + sizeOf b

instance : Ord HFSet := ⟨HFSet.cmp⟩
instance : BEq HFSet := ⟨fun a b => HFSet.cmp a b == .eq⟩

-- ================================================================
-- 3. OPERACIONES BÁSICAS
-- (SET primero en todos los argumentos para dot notation correcta)
-- ================================================================

def HFSet.empty : HFSet := HFSet.node []

-- s.insert x = insertar el elemento x en el conjunto s
def HFSet.insert (s : HFSet) (x : HFSet) : HFSet :=
  match s with
  | HFSet.node []       => HFSet.node [x]
  | HFSet.node (y :: ys) =>
      match HFSet.cmp x y with
      | .lt => HFSet.node (x :: y :: ys)
      | .eq => HFSet.node (y :: ys)         -- ya existe: sin duplicado
      | .gt => match (HFSet.node ys).insert x with
               | HFSet.node rest => HFSet.node (y :: rest)

-- s.mem x = ¿pertenece x al conjunto s?
def HFSet.mem (s : HFSet) (x : HFSet) : Bool :=
  match s with
  | HFSet.node []       => false
  | HFSet.node (y :: ys) =>
      match HFSet.cmp x y with
      | .lt => false                    -- ordenado: x no puede estar más a la derecha
      | .eq => true
      | .gt => (HFSet.node ys).mem x

def HFSet.elems : HFSet → List HFSet
  | HFSet.node xs => xs

def HFSet.card : HFSet → Nat
  | HFSet.node xs => xs.length

-- Construir desde lista (ordena y elimina duplicados)
def HFSet.ofList (xs : List HFSet) : HFSet :=
  xs.foldl (fun s x => s.insert x) HFSet.empty

-- ================================================================
-- 4. INSTANCIAS
-- ================================================================

instance : Membership HFSet HFSet where
  mem s x := HFSet.mem s x = true       -- s es el conjunto, x el elemento

instance {x s : HFSet} : Decidable (x ∈ s) :=
  show Decidable (HFSet.mem s x = true) from
    if h : HFSet.mem s x = true then .isTrue h else .isFalse h

instance : ToString HFSet where
  toString s :=
    let rec aux : HFSet → String
      | HFSet.node []  => "∅"
      | HFSet.node xs  =>
          "{" ++ (xs.map aux).foldl
            (fun acc e => if acc == "" then e else acc ++ ", " ++ e) ""
          ++ "}"
    aux s

instance : Repr HFSet where
  reprPrec s _ := toString s

-- ================================================================
-- 5. OPERACIONES DE CONJUNTOS
-- ================================================================

def HFSet.union (s t : HFSet) : HFSet :=
  s.elems.foldl (fun acc x => acc.insert x) t

def HFSet.inter (s t : HFSet) : HFSet :=
  s.elems.foldl (fun acc x =>
    if t.mem x then acc.insert x else acc) .empty

def HFSet.diff (s t : HFSet) : HFSet :=
  s.elems.foldl (fun acc x =>
    if t.mem x then acc else acc.insert x) .empty

def HFSet.subset (s t : HFSet) : Bool :=
  s.elems.all (t.mem ·)

-- Conjunto potencia: P(s) = todos los subconjuntos de s
-- P(∅)       = {∅}
-- P({x}∪A)   = P(A) ∪ { T∪{x} | T ∈ P(A) }
def HFSet.powerset : HFSet → HFSet
  | .node []       => .node [.node []]
  | .node (x :: xs) =>
      let ps := HFSet.powerset (.node xs)
      let withX := HFSet.ofList (ps.elems.map (fun t => t.insert x))
      ps.union withX

-- Separación: { x ∈ s | p(x) }
def HFSet.sep (p : HFSet → Bool) (s : HFSet) : HFSet :=
  HFSet.ofList (s.elems.filter p)

-- Unión generalizada: ⋃s = { x | ∃ t ∈ s, x ∈ t }
def HFSet.bigUnion (s : HFSet) : HFSet :=
  s.elems.foldl (fun acc t => acc.union t) .empty

-- ================================================================
-- 6. ORDINALES DE VON NEUMANN
-- ================================================================
-- 0 = ∅,  n+1 = n ∪ {n}  (insertar n como elemento en n mismo)

def vonNeumann : Nat → HFSet
  | 0     => .empty
  | n + 1 => let vn := vonNeumann n; vn.insert vn

-- ================================================================
-- 7. VERIFICACIONES
-- ================================================================

-- Ordinales:
#eval vonNeumann 0   -- ∅
#eval vonNeumann 1   -- {∅}
#eval vonNeumann 2   -- {∅, {∅}}
#eval vonNeumann 3   -- {∅, {∅}, {∅, {∅}}}
#eval vonNeumann 4   -- {∅, {∅}, {∅, {∅}}, {∅, {∅}, {∅, {∅}}}}

-- Cardinalidad = el natural que representa:
#eval (vonNeumann 4).card    -- 4

-- Pertenencia:
#eval (vonNeumann 3).mem (vonNeumann 2)   -- true  (2 ∈ 3)
#eval (vonNeumann 3).mem (vonNeumann 3)   -- false (3 ∉ 3, bien fundado)

-- Extensionalidad: mismo conjunto, distinto orden de construcción:
#eval vonNeumann 2 == HFSet.ofList [vonNeumann 1, vonNeumann 0]  -- true

-- Operaciones con s₁ = {0,1,2} = 3  y  s₂ = {1,2,3}:
private def s₁ := vonNeumann 3
private def s₂ := HFSet.ofList [vonNeumann 1, vonNeumann 2, vonNeumann 3]

#eval s!"s₁     = {s₁}"
#eval s!"s₂     = {s₂}"
#eval s!"s₁∪s₂  = {s₁.union s₂}"
#eval s!"s₁∩s₂  = {s₁.inter s₂}"
#eval s!"s₁\\s₂ = {s₁.diff  s₂}"
#eval s!"s₁⊆s₂? {s₁.subset s₂}"

-- Separación: los elementos no vacíos de 3
#eval s!"noVacíos(3) = {s₁.sep (fun x => !x.elems.isEmpty)}"

-- Conjunto potencia de 2:
#eval s!"P(2) = {HFSet.powerset (vonNeumann 2)}"
-- Esperado: {∅, {∅}, {{∅}}, {∅,{∅}}} — 4 subconjuntos

-- Unión generalizada: ⋃3 = ⋃{0,1,2} = ∅∪{∅}∪{∅,{∅}} = {∅,{∅}} = 2
#eval s!"⋃3 = {HFSet.bigUnion (vonNeumann 3)}"

-- ================================================================
-- MAIN
-- ================================================================

def main : IO Unit := do
  IO.println "=== Sesión 7: HFSet — Conjuntos Finitos Hereditarios ==="
  for n in List.range 5 do
    IO.println s!"vonNeumann {n} = {vonNeumann n}"
  IO.println s!"P(2)  = {HFSet.powerset (vonNeumann 2)}"
  IO.println s!"⋃3    = {HFSet.bigUnion (vonNeumann 3)}"
  IO.println s!"2 ∈ 3 = {(vonNeumann 3).mem (vonNeumann 2)}"
  IO.println s!"3 ∈ 3 = {(vonNeumann 3).mem (vonNeumann 3)}"
