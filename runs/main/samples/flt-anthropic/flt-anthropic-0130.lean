namespace P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom

set_option autoImplicit false

p2m_open

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar

open MeasureTheory

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar

open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell

namespace TateLocal

namespace Ws47Ramified

p2m_open

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem gauss_mul_term [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (ψ : AddChar (v.adicCompletion K) ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (t : v.adicCompletion K) {u' : v.adicCompletion K}
    (hu' : Valued.v u' = 1) :
    (∫ u in {u : v.adicCompletion K | Valued.v u = 1}, ψ (t * u) * charExt χ⁻¹ u ∂μ)
        * (ψ (t * u') * charExt χ u')
      = ∫ w in {u : v.adicCompletion K | Valued.v u = 1}, ψ (u' * (t * (w + 1))) * charExt χ⁻¹ w ∂μ := by
  have hu'0 : u' ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hu']; exact one_ne_zero)
  obtain ⟨c, rfl⟩ : ∃ c : (v.adicCompletion K)ˣ, (c : v.adicCompletion K) = u' :=
    ⟨Units.mk0 u' hu'0, Units.val_mk0 hu'0⟩
  have hmod : modulus (c : v.adicCompletion K) = 1 := modulus_eq_one_of_valued v hu'
  rw [setIntegral_comp_mul_left_of_modulus_eq_one μ hmod (fun u => ψ (t * u) * charExt χ⁻¹ u)
      (measurableSet_units_set v), preimage_mul_units_set v hu', ← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_units_set v) fun w _ => ?_
  have hχc : charExt χ (c : v.adicCompletion K) = (χ c : ℂ) := by
    rw [charExt_of_ne_zero χ c.ne_zero, Units.mk0_val]
  have hχχ : (χ⁻¹ c : ℂ) * (χ c : ℂ) = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
  have hψ : ψ (t * ((c : v.adicCompletion K) * w)) * ψ (t * (c : v.adicCompletion K))
      = ψ ((c : v.adicCompletion K) * (t * (w + 1))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  show ψ (t * ((c : v.adicCompletion K) * w)) * charExt χ⁻¹ ((c : v.adicCompletion K) * w)
      * (ψ (t * (c : v.adicCompletion K)) * charExt χ (c : v.adicCompletion K))
    = ψ ((c : v.adicCompletion K) * (t * (w + 1))) * charExt χ⁻¹ w
  rw [charExt_units_mul, hχc]
  linear_combination (charExt χ⁻¹ w * ((χ⁻¹ c : ℂ) * (χ c : ℂ))) * hψ
    + (ψ ((c : v.adicCompletion K) * (t * (w + 1))) * charExt χ⁻¹ w) * hχχ

end Kv
end Ws47Ramified
end TateLocal
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_TateLocal_setIntegral_addChar_mul_charExt_eq_zero_of_valued_ne
