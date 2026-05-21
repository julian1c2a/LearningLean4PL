import Lean

inductive CList : Type where
  | mk : List CList → CList
  deriving Repr, Inhabited

namespace CList

inductive CListOp | mem | subset | eq

@[simp] def opWeight : CListOp → Nat | .mem => 0 | .subset => 1 | .eq => 2

def evalOp (op : CListOp) (A B : CList) : Bool :=
  match op, A, B with
  | .mem, _, mk []          => false
  | .mem, x, mk (y :: ys)   => evalOp .eq x y || evalOp .mem x (mk ys)
  | .subset, mk [], _       => true
  | .subset, mk (x :: xs), B => evalOp .mem x B && evalOp .subset (mk xs) B
  | .eq, A, B               => evalOp .subset A B && evalOp .subset B A
termination_by (((sizeOf A + sizeOf B : Nat) * 3) + opWeight op : Nat)
decreasing_by all_goals simp_wf; all_goals try simp [sizeOf]; all_goals try omega

def extEq (A B : CList) : Bool := evalOp .eq A B
def subset (A B : CList) : Bool := evalOp .subset A B
def mem (x B : CList) : Bool := evalOp .mem x B

theorem extEq_def (A B : CList) : extEq A B = (subset A B && subset B A) := by simp only [extEq, subset, evalOp]
theorem subset_nil (B : CList) : subset (mk []) B = true := by simp only [subset, evalOp]
theorem subset_cons (x : CList) (xs : List CList) (B : CList) : subset (mk (x :: xs)) B = (mem x B && subset (mk xs) B) := by simp only [subset, mem, evalOp]
theorem mem_nil (x : CList) : mem x (mk []) = false := by simp only [mem, evalOp]
theorem mem_cons (x y : CList) (ys : List CList) : mem x (mk (y :: ys)) = (extEq x y || mem x (mk ys)) := by simp only [mem, extEq, evalOp]

theorem subset_mono (xs : List CList) (y : CList) (ys : List CList) (h : subset (mk xs) (mk ys) = true) : subset (mk xs) (mk (y :: ys)) = true := by
  induction xs with
  | nil      => simp [subset_nil]
  | cons z zs ih =>
    simp only [subset_cons, Bool.and_eq_true] at h ⊢
    exact ⟨by simp [mem_cons, h.1], ih h.2⟩

theorem subset_refl (A : CList) : subset A A = true := by
  match A with
  | mk [] => simp [subset_nil]
  | mk (x :: xs) =>
    have hx  : subset x x = true             := subset_refl x
    have hxs : subset (mk xs) (mk xs) = true := subset_refl (mk xs)
    simp only [subset_cons, Bool.and_eq_true]
    exact ⟨by simp [mem_cons, extEq_def, hx], subset_mono xs x xs hxs⟩
termination_by sizeOf A
decreasing_by all_goals simp_wf; all_goals try simp [sizeOf]; all_goals try omega

theorem extEq_refl (A : CList) : extEq A A = true := by
  simp only [extEq_def, Bool.and_eq_true]
  exact ⟨subset_refl A, subset_refl A⟩

theorem extEq_symm {A B : CList} (h : extEq A B = true) : extEq B A = true := by
  simp only [extEq_def, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

mutual
  theorem extEq_trans : (A B C : CList) → extEq A B = true → extEq B C = true → extEq A C = true
    | A, B, C, h1, h2 => by
        simp only [extEq_def, Bool.and_eq_true] at h1 h2 ⊢
        exact ⟨subset_trans A B C h1.1 h2.1, subset_trans C B A h2.2 h1.2⟩
  termination_by A B C _ _ => (sizeOf A + sizeOf B + sizeOf C) * 2 + 1
  decreasing_by all_goals simp_wf; all_goals try simp [sizeOf]; all_goals try omega

  theorem subset_trans : (A B C : CList) → subset A B = true → subset B C = true → subset A C = true
    | mk [], _, _, _, _ => subset_nil _
    | mk (x :: xs), B, C, h1, h2 => by
        simp only [subset_cons, Bool.and_eq_true] at h1 ⊢
        exact ⟨mem_subset x B C h1.1 h2, subset_trans (mk xs) B C h1.2 h2⟩
  termination_by A B C _ _ => (sizeOf A + sizeOf B + sizeOf C) * 2
  decreasing_by all_goals simp_wf; all_goals try simp [sizeOf]; all_goals try omega

  theorem mem_subset : (x B C : CList) → mem x B = true → subset B C = true → mem x C = true
    | _, mk [], _, h1, _ => by simp [mem_nil] at h1
    | x, mk (y :: ys), C, h1, h2 => by
        simp only [mem_cons, Bool.or_eq_true] at h1
        simp only [subset_cons, Bool.and_eq_true] at h2
        cases h1 with
        | inl h1_eq  => exact mem_of_extEq x y C h1_eq h2.1
        | inr h1_mem => exact mem_subset x (mk ys) C h1_mem h2.2
  termination_by x B C _ _ => (sizeOf x + sizeOf B + sizeOf C) * 2
  decreasing_by all_goals simp_wf; all_goals try simp [sizeOf]; all_goals try omega

  theorem mem_of_extEq : (x y C : CList) → extEq x y = true → mem y C = true → mem x C = true
    | _, _, mk [], _, h2 => by simp [mem_nil] at h2
    | x, y, mk (z :: zs), h1, h2 => by
        simp only [mem_cons, Bool.or_eq_true] at h2 ⊢
        cases h2 with
        | inl h2_eq  => exact Or.inl (extEq_trans x y z h1 h2_eq)
        | inr h2_mem => exact Or.inr (mem_of_extEq x y (mk zs) h1 h2_mem)
  termination_by x y C _ _ => (sizeOf x + sizeOf y + sizeOf C) * 2
  decreasing_by all_goals simp_wf; all_goals try simp [sizeOf]; all_goals try omega
end

end CList
