@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing UnitriangularCoordinateRing

open scoped TensorProduct

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

theorem ideal_zero : ideal K n 0 = ⊥ := by
  apply le_bot_iff.mp
  apply Ideal.span_le.mpr
  rintro _ ⟨i, j, hij, hgap, rfl⟩
  omega

end UnitriangularStageCoordinateRing
end
end
