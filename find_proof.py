import subprocess

lean_code = """
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

-- Using Ordinal.rec to bypass termination checker
def le_trans (β : Ordinal) : ∀ {α γ : Ordinal}, OrdLe α β → OrdLe β γ → OrdLe α γ :=
  Ordinal.rec
    (fun α γ h1 h2 => 
      match h1 with
      | OrdLe.zero_le _ => OrdLe.zero_le γ
      | OrdLe.sup_le h_le => 
        OrdLe.sup_le (fun i => 
          -- wait, we don't have ih for h_le i because β is zero!
          sorry))
    (fun b ih α γ h1 h2 => sorry)
    (fun α f ih α' γ h1 h2 => sorry)
    β
"""

with open("temp.lean", "w", encoding="utf-8") as f:
    f.write(lean_code)

with open("out.txt", "w", encoding="utf-8") as out:
    subprocess.run(["lean", "temp.lean"], stdout=out, stderr=subprocess.STDOUT, text=True, encoding="utf-8")
