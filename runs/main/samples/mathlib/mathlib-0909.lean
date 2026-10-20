@[expose] public section

open Order

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

@[nontriviality]
lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] : ringKrullDim R = ⊥ :=
  krullDim_eq_bot

end
