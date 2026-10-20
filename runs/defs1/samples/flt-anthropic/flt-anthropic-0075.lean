namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

section

set_option autoImplicit false

open Polynomial

p2m_reactivate

namespace GaussPencil

open Polynomial

p2m_reactivate

section Theta

variable {L K₁ : Type*} [Field L] [Field K₁] [Algebra L K₁]
  (A : ValuationSubring L) (V : ValuationSubring K₁)
  (hVA : ∀ c : L, algebraMap L K₁ c ∈ V ↔ c ∈ A)
  (e₁ : RatFunc L ≃ₐ[L] K₁) (hX : e₁ RatFunc.X ∈ V)
  [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)]
  (hψ : ∀ a : A, algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) (IsLocalRing.residue A a)
    = IsLocalRing.residue V ⟨algebraMap L K₁ a, (hVA a).mpr a.2⟩)
  (htr : Transcendental (IsLocalRing.ResidueField A) (IsLocalRing.residue V ⟨e₁ RatFunc.X, hX⟩))
  {k : Type*} [Field k] (σ : IsLocalRing.ResidueField A →+* k)

noncomputable def ratFuncMap : RatFunc (IsLocalRing.ResidueField A) →+* RatFunc k :=
  RatFunc.liftRingHom ((algebraMap k[X] (RatFunc k)).comp (mapRingHom σ)) (by
    intro p hp
    simp only [Submonoid.mem_comap, RingHom.coe_comp, Function.comp_apply, mem_nonZeroDivisors_iff_ne_zero]
    exact RatFunc.algebraMap_ne_zero ((Polynomial.map_ne_zero_iff σ.injective).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hp)))

end Theta
end GaussPencil
end
end P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots
