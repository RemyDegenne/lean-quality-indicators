@[expose] public section

universe u v w

namespace Module

section AddCommMonoid

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R M}

section TensorProduct

open scoped TensorProduct

variable {N : Type w} [AddCommMonoid N] [Module R N]

theorem IsKilledByIdealPower.tensorProduct_left {I : Ideal R}
    (hM : IsKilledByIdealPower R M I) : IsKilledByIdealPower R (M ⊗[R] N) I := by
  obtain ⟨n, hn⟩ := hM
  exact ⟨n, hn.tensorProduct_left⟩

end TensorProduct
end AddCommMonoid
end Module
end
