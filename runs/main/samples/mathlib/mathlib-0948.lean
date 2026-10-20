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

theorem LinearIndependent.smul_left_injective (hv : LinearIndependent R v) (i : ι) :
    Injective fun r : R ↦ r • v i := by convert! hv.comp (Finsupp.single_injective i); simp

end Semiring
end
end
