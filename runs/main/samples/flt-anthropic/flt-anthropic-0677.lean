namespace P2MW.S_ModularCurve_heckeOperatorOneBar_comm

attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped IntermediateField MatrixGroups

p2m_reactivate

namespace X1HeckeCommRoof

p2m_open

open X1HeckeCommGeneric X1HeckeCommFields

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

scoped instance neZero_mul_level : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩

scoped instance neZero_top_level : NeZero (M * ℓ * ℓ') :=
  ⟨mul_ne_zero (mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)) (NeZero.ne ℓ')⟩

scoped instance charZero_sub (A : IntermediateField L (LaurentSeries L)) : CharZero A := by
  haveI : CharZero L := charZero_base L
  exact charZero_of_injective_algebraMap (algebraMap L A).injective

variable {L M ℓ ℓ'}

variable (L M ℓ ℓ')

theorem nice_KT' : Nice L M ℓ ℓ' (KT L M (M * ℓ')) :=
  (nice_KK L M ℓ ℓ').mono (KK_le_KT L M _) (KT_mono L M ⟨ℓ, by ring⟩)

end X1HeckeCommRoof
end
end P2MW.S_ModularCurve_heckeOperatorOneBar_comm
