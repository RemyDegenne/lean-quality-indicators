@[expose] public section

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}

variable {M : Type*} {M' : Type*} {V : Type u}

section Module

variable [Ring R] [AddCommGroup M] [AddCommGroup M']

variable [Module R M] [Module R M']

variable {v : ι → M} {i : ι}

open LinearMap

variable [IsDomain R] [IsTorsionFree R M]

lemma LinearIndependent.of_subsingleton [Subsingleton ι] (i : ι) (hi : v i ≠ 0) :
    LinearIndependent R v := .of_subsingleton' i (by simp [hi])

end Module
end
end
