public section

open IsLocalRing

namespace WeierstrassCurve.Affine.Point

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W]
  [(integralModel v.valuationSubring W).IsElliptic]

variable [DecidableEq F]

variable [DecidableEq (ResidueField v.valuationSubring)]

theorem reductionHom_some_of_valuation_le_one {x y : F} (h : W.Nonsingular x y) (hx : v x ≤ 1)
    (h' : ((integralModel v.valuationSubring W).map
      (residue v.valuationSubring)).toAffine.Nonsingular
        (residue _ ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩)
        (residue _ ⟨y, (v.mem_valuationSubring_iff y).mpr
          (valuation_y_le_one_of_valuation_x_le_one v h.left hx)⟩)) :
    reductionHom v (some x y h) = some _ _ h' := by
  rw [reductionHom_apply v _ ((some_mem_nonsingularReduction_iff v h hx).mpr h')]
  exact nonsingularReductionHom_some_of_valuation_le_one v h hx h'

end WeierstrassCurve.Affine.Point
end
