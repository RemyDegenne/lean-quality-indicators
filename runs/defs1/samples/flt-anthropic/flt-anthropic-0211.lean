namespace P2MW.S_ModularCurve_heckeInputsHAlong

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeInputsHAll

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix AlgebraicCurve IntermediateField HahnSeries

section LevelRaise

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]

def levelRaise {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm ((CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (inf_le_conj (NeZero.ne ℓ)) (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

end LevelRaise
end HeckeInputsHAll
end
end P2MW.S_ModularCurve_heckeInputsHAlong
