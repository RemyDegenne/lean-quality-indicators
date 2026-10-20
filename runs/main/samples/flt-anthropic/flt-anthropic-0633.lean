namespace P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

p2m_open

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable (W : WeierstrassCurve A)

namespace Affine p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Nonsingular Point.some.inj negAddY negY_negY equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff polynomial Point.neg_some" end Affine

p2m_open_scoped "WeierstrassCurve.Affine" in

p2m_open_scoped "WeierstrassCurve.Affine" in

p2m_open_scoped "WeierstrassCurve.Affine" in

variable {W}

variable (hΔ : (W.map (residue A)).Δ ≠ 0)

lemma reducePoint_some_of_mem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    reducePoint hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) := by
  simp only [reducePoint]
  exact dif_pos hx

end Affine
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia
