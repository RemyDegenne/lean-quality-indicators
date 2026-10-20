namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology

open scoped NNReal ENNReal

p2m_reactivate

p2m_reactivate

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace S1Q

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem map_mul_left_eq_smul [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure] (u : (F)ˣ) :
    ν.map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : (F)ˣ) : F) • s := by
    rw [smul_set_eq_preimage p (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : (F)ˣ) • s : Set F) = ((u⁻¹ : (F)ˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

end Main
end S1Q
end
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
