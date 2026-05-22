import Init.Core

#check Quotient.sound
#check Quot.sound

noncomputable def getRep {α : Sort u} [Setoid α] (q : Quotient ‹Setoid α›) : α :=
  Classical.choose (Quotient.exists_rep q)
