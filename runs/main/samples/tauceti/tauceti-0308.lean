public section

open QuadraticMap

namespace TauCeti.QuadraticMap

open _root_.CliffordAlgebra TauCeti.QuadraticMap

variable {R M₁ M₂ : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

@[simp↓]
theorem spinToOrthogonal_spinGroupEquiv [Invertible (2 : R)]
    (e : Q₁.IsometryEquiv Q₂) (x : spinGroup Q₁) :
    spinToOrthogonal Q₂ (e.spinGroupEquiv x) =
      e.orthogonalGroupCongr (spinToOrthogonal Q₁ x) := by
  rw [← specialOrthogonalToOrthogonal_spinToSpecialOrthogonal,
    ← e.specialOrthogonalGroupCongr_spinToSpecialOrthogonal,
    e.specialOrthogonalToOrthogonal_specialOrthogonalGroupCongr,
    specialOrthogonalToOrthogonal_spinToSpecialOrthogonal]

end TauCeti.QuadraticMap
end
