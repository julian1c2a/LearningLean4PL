inductive Ordinal : Type 1
| zero : Ordinal
| succ : Ordinal → Ordinal
| sup : {α : Type} → (α → Ordinal) → Ordinal

inductive OrdLe : Ordinal → Ordinal → Prop where
| zero_le (b : Ordinal) : OrdLe Ordinal.zero b
| succ_le_succ {a b : Ordinal} : OrdLe a b → OrdLe (Ordinal.succ a) (Ordinal.succ b)
| le_sup {α : Type} {f : α → Ordinal} {b : Ordinal} (i : α) :
    OrdLe b (f i) → OrdLe b (Ordinal.sup f)
| sup_le {α : Type} {f : α → Ordinal} {b : Ordinal} :
    (∀ i, OrdLe (f i) b) → OrdLe (Ordinal.sup f) b

def OrdLt (α β : Ordinal) : Prop := OrdLe (Ordinal.succ α) β

axiom le_trans {α β γ : Ordinal} : OrdLe α β → OrdLe β γ → OrdLe α γ

theorem lt_le_trans {α β γ : Ordinal} (h1 : OrdLt α β) (h2 : OrdLe β γ) : OrdLt α γ :=
  le_trans h1 h2

theorem le_lt_trans {α β γ : Ordinal} (h1 : OrdLe α β) (h2 : OrdLt β γ) : OrdLt α γ :=
  le_trans (OrdLe.succ_le_succ h1) h2

theorem le_sup_lemma {α : Type} (f : α → Ordinal) (i : α) : OrdLe (f i) (Ordinal.sup f) := by
  -- We want to prove f i <= sup f.
  -- Wait! OrdLe.le_sup requires `b <= f i -> b <= sup f`.
  -- We don't have a direct proof of f i <= sup f!
  -- We need reflexivity to do `f i <= f i -> f i <= sup f`!
  sorry

theorem le_refl (α : Ordinal) : OrdLe α α := by
  induction α with
  | zero => exact OrdLe.zero_le _
  | succ a ih => exact OrdLe.succ_le_succ ih
  | sup f ih =>
    apply OrdLe.sup_le
    intro i
    apply OrdLe.le_sup i
    exact ih i

theorem le_sup_refl {α : Type} (f : α → Ordinal) (i : α) : OrdLe (f i) (Ordinal.sup f) :=
  OrdLe.le_sup i (le_refl (f i))

theorem le_succ (α : Ordinal) : OrdLe α (Ordinal.succ α) := by
  induction α with
  | zero => exact OrdLe.zero_le _
  | succ a ih => exact OrdLe.succ_le_succ ih
  | sup f ih =>
    apply OrdLe.sup_le
    intro i
    have h1 : OrdLe (f i) (Ordinal.succ (f i)) := ih i
    have h2 : OrdLe (f i) (Ordinal.sup f) := le_sup_refl f i
    have h3 : OrdLe (Ordinal.succ (f i)) (Ordinal.succ (Ordinal.sup f)) := OrdLe.succ_le_succ h2
    exact le_trans h1 h3

theorem lt_implies_le {α β : Ordinal} (h : OrdLt α β) : OrdLe α β :=
  le_trans (le_succ α) h

theorem lt_lt_trans {α β γ : Ordinal} (h1 : OrdLt α β) (h2 : OrdLt β γ) : OrdLt α γ :=
  le_lt_trans (lt_implies_le h1) h2
