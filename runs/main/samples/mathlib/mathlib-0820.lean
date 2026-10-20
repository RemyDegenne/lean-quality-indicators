@[expose] public section

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}

variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring

variable {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M] [Module R M']

variable (R) (v)

variable {R v}

lemma LinearIndependent.isCompl_span_image (h₁ : LinearIndependent R v)
    (h₂ : Submodule.span R (Set.range v) = ⊤) {s t : Set ι} (hst : IsCompl s t) :
    IsCompl (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) :=
  ⟨h₁.disjoint_span_image hst.1, Submodule.codisjoint_span_image_of_codisjoint h₂ hst.2⟩

end Semiring
end
end
