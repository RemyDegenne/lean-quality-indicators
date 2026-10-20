@[expose] public section

open Module

variable {ι : Type*} [DecidableEq ι]

variable {R : Type*} [Ring R]

variable {A : Subring R}

@[simp]
lemma Subtype.val_comp_single (i : ι) (a : A) :
    Subtype.val ∘ Pi.single i a = Pi.single i a := by
  ext j
  by_cases h : i = j <;> aesop

end
