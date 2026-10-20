namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1_mul

attribute [-instance] WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

noncomputable section

p2m_open

open scoped MatrixGroups ModularForm

namespace INVOL

variable {N : ℕ}

section Ratio

variable {p : ℕ} {γ : SL(2, ℤ)} {Lc : Subfield ℂ}

structure WData (p : ℕ) (γ : SL(2, ℤ)) (Lc : Subfield ℂ) {k : ℤ} (f : MF N k) where
  D : ℤ
  hD : D ≠ 0
  φ : MF N k
  hφ : φ ∈ LForms Lc k
  eq : (⇑φ : ℍ → ℂ) = (D : ℂ) • Wfun p γ k ⇑f

end Ratio
end INVOL
end
end P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
