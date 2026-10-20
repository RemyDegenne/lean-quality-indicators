public section

open _root_.QuadraticMap

namespace QuadraticMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

theorem Equivalent.unitValueSet_eq
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ R} {Q₂ : QuadraticMap R M₂ R}
    (h : Q₁.Equivalent Q₂) : unitValueSet Q₁ = unitValueSet Q₂ := by
  obtain ⟨e⟩ := h
  ext a
  rw [mem_unitValueSet, mem_unitValueSet]
  exact e.represents_iff a

end QuadraticMap
end
