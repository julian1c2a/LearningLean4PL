inductive ZFCTree where
| replace {α : Type} (f : α → ZFCTree) : ZFCTree

def ZFCTree.equiv : ZFCTree → ZFCTree → Prop
| ZFCTree.replace f, ZFCTree.replace g =>
  (∀ i, ∃ j, ZFCTree.equiv (f i) (g j)) ∧
  (∀ j, ∃ i, ZFCTree.equiv (f i) (g j))

instance ZFCTree.setoid : Setoid ZFCTree where
  r := ZFCTree.equiv
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry
  }

def ZFCSet : Type 1 := Quotient ZFCTree.setoid
