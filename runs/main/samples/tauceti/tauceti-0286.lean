public section

open TauCeti TauCeti.Comodule

open scoped TensorProduct

namespace Module.Basis

universe u v w x

noncomputable section

variable {R : Type u} {C : Type v} {M : Type w} {ι : Type x}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M] [Comodule R C M]

@[simp]
theorem coordinateSpanIsStable_iff (b : Basis ι R M) (s : Set ι) :
    b.coordinateSpanIsStable (C := C) s ↔
      ∀ i, i ∉ s → ∀ j, j ∈ s → coefficientMatrix (C := C) b i j = 0 :=
  Iff.rfl

end
end Module.Basis
end
