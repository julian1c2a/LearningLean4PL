-- Construcción alternativa: ZFC (axiomas + conjuntos)
inductive ZFCTree where
| replace {α : Type} (f : α → ZFCTree) : ZFCTree -- axioma de reemplazamiento

-- El conjunto de los números naturales de Von Neumann dentro de ZFC
-- 0 = {} (conjunto vacío)
def ZFCTree.empty : ZFCTree :=
  ZFCTree.replace (α := Empty) Empty.rec

def ZFCTree.singleton (x : ZFCTree) : ZFCTree :=
  ZFCTree.replace (α := Unit) (fun _ => x)

-- Conjunto finito (usando una lista/vector como mapeo subyacente o una función sobre Fin n)
-- Conjunto infinito numerable (ej: el conjunto de todos los naturales modelados como WSets)
-- Primero definimos el conjunto finito para cualquier ordinal n = {0, 1, ..., n-1}
-- Un conjunto de n elementos tiene n ramas (Fin n), y cada rama i apunta al ordinal i
def ZFCTree.ofNat (n : Nat) : ZFCTree :=
  ZFCTree.replace (α := Fin n) (fun i => ZFCTree.ofNat i.val)
termination_by n  -- Le decimos a Lean que esto no es un bucle infinito porque i.val < n

-- Conjunto infinito numerable (el ordinal omega = {0, 1, 2, ...})
-- Tiene infinitas ramas (Nat), y cada rama n apunta al ordinal finito n
def ZFCTree.omega : ZFCTree :=
  ZFCTree.replace (α := Nat) (fun n => ZFCTree.ofNat n)

-- Representa un conjunto finito de naturales a partir de una lista
def ZFCTree.fromListNat (L : List Nat) : ZFCTree :=
  ZFCTree.replace (α := Fin L.length) (fun i => ZFCTree.ofNat (L.get i))

-- Dos conjuntos son equivalentes si para cada rama del primero existe una
-- rama equivalente en el segundo, y viceversa.
-- Lean detecta automáticamente la terminación porque `f i` y `g j` son estrictamente menores.
def ZFCTree.equiv : ZFCTree → ZFCTree → Prop
| ZFCTree.replace f, ZFCTree.replace g =>
  (∀ i, ∃ j, ZFCTree.equiv (f i) (g j)) ∧
  (∀ j, ∃ i, ZFCTree.equiv (f i) (g j))

-- Un elemento pertenece a un conjunto si equivale a alguna de sus ramas.
-- Ya no necesitamos recursión mutua.
def ZFCTree.mem (x a : ZFCTree) : Prop :=
  match a with
  | ZFCTree.replace f => ∃ i, ZFCTree.equiv x (f i)

-- Demostración de reflexividad usando inducción estructural
theorem ZFCTree.equiv_refl (x : ZFCTree) : ZFCTree.equiv x x := by
  induction x with
  | replace f ih =>
    -- Lean expande `equiv (replace f) (replace f)` en su definición (el AND ∧)
    -- `ih` es nuestra hipótesis inductiva: ∀ i, ZFCTree.equiv (f i) (f i)
    constructor
    · intro i; exact ⟨i, ih i⟩ -- Para todo i, existe un j (que es el mismo i), tal que son equivalentes
    · intro j; exact ⟨j, ih j⟩ -- Lo mismo para la otra dirección

-- Demostración de simetría usando inducción estructural
theorem ZFCTree.equiv_symm {x y : ZFCTree} :
  ZFCTree.equiv x y → ZFCTree.equiv y x
    := by
  -- Usamos `generalizing y` para que la hipótesis inductiva aplique a cualquier otro árbol,
  -- no solo al `y` fijo original (ya que necesitamos comparar `f i` con las ramas `g j`).
  induction x generalizing y with
  | replace f ih =>
    intro h
    cases y with
    | replace g =>
      -- Lean expande `equiv (replace f) (replace g)` a su conjunción de ∀ y ∃
      constructor
      · intro j
        -- Para cada j en g, necesitamos un i en f. Usamos la segunda parte de h (`h.right`).
        have ⟨i, hij⟩ := h.right j
        -- Al pasar `hij`, Lean infiere automáticamente que el argumento implícito {y} es `g j`
        exact ⟨i, ih i hij⟩
      · intro i
        have ⟨j, hij⟩ := h.left i
        exact ⟨j, ih i hij⟩

def ZFCTree.equiv_trans {x y z : ZFCTree} :
  ZFCTree.equiv x y → ZFCTree.equiv y z → ZFCTree.equiv x z := by
  intro h1 h2
  induction x generalizing y z with
  | replace f ih =>
    cases y with
    | replace g =>
      cases z with
      | replace h =>
        --let h1 : equiv (replace f) (replace g)
        --let h2 : equiv (replace g) (replace h)
        constructor
        · intro i -- i is in f
          have ⟨j, hij⟩ := h1.left i -- j is in g
          have ⟨k, hjk⟩ := h2.left j -- k is in h
          exact ⟨k, ih i hij hjk⟩
        · intro k -- k is in h
          have ⟨j, hjk⟩ := h2.right k -- j is in g
          have ⟨i, hij⟩ := h1.right j -- i is in f
          exact ⟨i, ih i hij hjk⟩

-- Agrupamos la relación y demostramos que es de equivalencia
-- Usamos `instance` en lugar de `def` para habilitar la notación matemática ⟦ ⟧
instance ZFCTree.setoid : Setoid ZFCTree where
  r := ZFCTree.equiv
  iseqv := {
    refl := ZFCTree.equiv_refl
    symm := ZFCTree.equiv_symm
    trans := ZFCTree.equiv_trans
  }

-- ¡Aquí está el verdadero tipo de los Conjuntos de ZFC!
-- Un conjunto es simplemente la clase de equivalencia de los árboles.
def ZFCSet : Type 1 := Quotient ZFCTree.setoid

-- Demostración de que la relación de pertenencia en ZFCTree respeta la equivalencia
theorem ZFCTree.mem_congr (a₁ b₁ a₂ b₂ : ZFCTree)
  (ha : ZFCTree.equiv a₁ a₂) (hb : ZFCTree.equiv b₁ b₂) :
  ZFCTree.mem a₁ b₁ = ZFCTree.mem a₂ b₂ := by
  apply propext
  cases b₁ with | replace f =>
  cases b₂ with | replace g =>
  constructor
  · intro ⟨i, hi⟩
    have ⟨j, hij⟩ := hb.left i
    have h1 := ZFCTree.equiv_trans (ZFCTree.equiv_symm ha) hi
    exact ⟨j, ZFCTree.equiv_trans h1 hij⟩
  · intro ⟨j, hj⟩
    have ⟨i, hij⟩ := hb.right j
    have h1 := ZFCTree.equiv_trans hj (ZFCTree.equiv_symm hij)
    exact ⟨i, ZFCTree.equiv_trans ha h1⟩

-- Levantamos la función de pertenencia de ZFCTree a ZFCSet.
def ZFCSet.mem (x A : ZFCSet) : Prop :=
  Quotient.lift₂ ZFCTree.mem ZFCTree.mem_congr x A

-- ¡Aquí ocurre la magia de la notación! Vinculamos nuestra función a la clase Membership.
instance : Membership ZFCSet ZFCSet where
  mem := ZFCSet.mem

-- Definición de subconjunto (A ⊆ B): Todo elemento de A también pertenece a B
def ZFCSet.subset (A B : ZFCSet) : Prop :=
  ∀ x, x ∈ A → x ∈ B

-- Subconjunto estricto (A ⊂ B): A es subconjunto de B, pero B no es subconjunto de A
def ZFCSet.ssubset (A B : ZFCSet) : Prop :=
  ZFCSet.subset A B ∧ ¬(ZFCSet.subset B A)

-- Superconjunto (A ⊇ B): B es subconjunto de A
def ZFCSet.supset (A B : ZFCSet) : Prop :=
  ZFCSet.subset B A

-- Superconjunto estricto (A ⊃ B): B es subconjunto estricto de A
def ZFCSet.ssupset (A B : ZFCSet) : Prop :=
  ZFCSet.ssubset B A

-- Vinculamos las funciones a su simbología estándar
notation:50 A " ⊆ " B => ZFCSet.subset A B
notation:50 A " ⊂ " B => ZFCSet.ssubset A B
notation:50 A " ⊇ " B => ZFCSet.supset A B
notation:50 A " ⊃ " B => ZFCSet.ssupset A B

-- El conjunto vacío a nivel de ZFCSet (la clase de equivalencia del árbol vacío)
def ZFCSet.empty : ZFCSet :=
  Quotient.mk ZFCTree.setoid ZFCTree.empty
