/-!
Sesión 8: ZFC en un universo explícito

Idea:
- Esta sesión está parametrizada por un universo `u`.
- `ZFCTree` vive en `Type (u+1)` y sus ramas usan índices en `Type u`.
- Así obtenemos una versión de la construcción en cada nivel de universo.
-/

universe u

-- Construcción alternativa: ZFC (axiomas + conjuntos)
inductive ZFCTree : Type (u+1) where
  | replace {α : Type u} (f : α → ZFCTree) : ZFCTree

namespace ZFCTree

-- Conjunto vacío en el universo actual.
def empty : ZFCTree :=
  ZFCTree.replace (α := PEmpty) (fun e => nomatch e)

-- Singleton.
def singleton (x : ZFCTree) : ZFCTree :=
  ZFCTree.replace (α := Unit) (fun _ => x)

-- Von Neumann finito: n = {0,1,...,n-1}
def ofNat (n : Nat) : ZFCTree :=
  ZFCTree.replace (α := Fin n) (fun i => ofNat i.val)
termination_by n

-- Omega (infinito numerable): {0,1,2,...}
def omega : ZFCTree :=
  ZFCTree.replace (α := Nat) (fun n => ofNat n)

-- Conjunto finito de naturales desde lista
def fromListNat (L : List Nat) : ZFCTree :=
  ZFCTree.replace (α := Fin L.length) (fun i => ofNat (L.get i))

-- Extensionalidad bisimulada
def equiv : ZFCTree → ZFCTree → Prop
  | .replace f, .replace g =>
      (∀ i, ∃ j, equiv (f i) (g j)) ∧
      (∀ j, ∃ i, equiv (f i) (g j))

-- Pertenencia
def mem (x a : ZFCTree) : Prop :=
  match a with
  | .replace f => ∃ i, equiv x (f i)

theorem equiv_refl (x : ZFCTree) : equiv x x := by
  induction x with
  | replace f ih =>
      constructor
      · intro i; exact ⟨i, ih i⟩
      · intro j; exact ⟨j, ih j⟩

theorem equiv_symm {x y : ZFCTree} : equiv x y → equiv y x := by
  induction x generalizing y with
  | replace f ih =>
      intro h
      cases y with
      | replace g =>
          constructor
          · intro j
            have ⟨i, hij⟩ := h.right j
            exact ⟨i, ih i hij⟩
          · intro i
            have ⟨j, hij⟩ := h.left i
            exact ⟨j, ih i hij⟩

-- Transitividad (teorema; no la necesitamos computacionalmente)
theorem equiv_trans {x y z : ZFCTree} : equiv x y → equiv y z → equiv x z := by
  intro h1 h2
  induction x generalizing y z with
  | replace f ih =>
      cases y with
      | replace g =>
          cases z with
          | replace h =>
              constructor
              · intro i
                have ⟨j, hij⟩ := h1.left i
                have ⟨k, hjk⟩ := h2.left j
                exact ⟨k, ih i hij hjk⟩
              · intro k
                have ⟨j, hjk⟩ := h2.right k
                have ⟨i, hij⟩ := h1.right j
                exact ⟨i, ih i hij hjk⟩

instance setoid : Setoid ZFCTree where
  r := equiv
  iseqv := {
    refl  := equiv_refl
    symm  := equiv_symm
    trans := equiv_trans
  }

end ZFCTree

-- Conjuntos ZFC = cociente por extensionalidad
def ZFCSet : Type (u+1) := Quotient ZFCTree.setoid

namespace ZFCSet

-- Pertenencia levantada al cociente
def mem (x A : ZFCSet) : Prop :=
  Quotient.lift₂
    ZFCTree.mem
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      apply propext
      constructor
      · intro h
        cases b₁ with
        | replace f =>
            cases b₂ with
            | replace g =>
                rcases h with ⟨i, hi⟩
                rcases hb.left i with ⟨j, hij⟩
                have h1 := ZFCTree.equiv_trans (ZFCTree.equiv_symm ha) hi
                exact ⟨j, ZFCTree.equiv_trans h1 hij⟩
      · intro h
        cases b₁ with
        | replace f =>
            cases b₂ with
            | replace g =>
                rcases h with ⟨j, hj⟩
                rcases hb.right j with ⟨i, hij⟩
                have h1 := ZFCTree.equiv_trans hj (ZFCTree.equiv_symm hij)
                exact ⟨i, ZFCTree.equiv_trans ha h1⟩)
    x A

instance : Membership ZFCSet ZFCSet where
  mem := mem

-- Relaciones entre conjuntos
def subset (A B : ZFCSet.{u}) : Prop :=
  ∀ x : ZFCSet.{u}, x ∈ A → x ∈ B

def ssubset (A B : ZFCSet.{u}) : Prop :=
  subset A B ∧ ¬ subset B A

def supset (A B : ZFCSet.{u}) : Prop :=
  subset B A

def ssupset (A B : ZFCSet.{u}) : Prop :=
  ssubset B A

notation:50 A " ⊆ " B => subset A B
notation:50 A " ⊂ " B => ssubset A B
notation:50 A " ⊇ " B => supset A B
notation:50 A " ⊃ " B => ssupset A B

-- Vacío y ejemplo "todos los tipos de Type u"
def empty : ZFCSet := Quotient.mk _ ZFCTree.empty

def allTypesSet : ZFCSet :=
  let tree : ZFCTree := ZFCTree.replace (α := Type u) (fun _ => ZFCTree.empty)
  Quotient.mk _ tree

end ZFCSet

-- Checks rápidos
#check ZFCTree        -- : Type (u+1)
#check (Type u)       -- : Type (u+1)
#check ZFCSet.allTypesSet

-- Mini sección: comparación entre niveles de universo
#check (ZFCTree.{0})
#check (ZFCTree.{1})
#check (ZFCSet.{0})
#check (ZFCSet.{1})

#check (ZFCSet.allTypesSet.{0})
#check (ZFCSet.allTypesSet.{1})

private def demoU0 : List ZFCTree.{0} :=
  [ZFCTree.ofNat 0, ZFCTree.ofNat 1, ZFCTree.ofNat 2]

#eval demoU0.length   -- 3

def main : IO Unit := do
  IO.println "=== Sesión 8: ZFC por niveles de universo ==="
  IO.println "Compila correctamente con universo explícito u."
