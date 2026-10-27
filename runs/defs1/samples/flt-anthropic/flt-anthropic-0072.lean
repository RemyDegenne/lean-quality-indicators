namespace P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

noncomputable section

namespace WhitIBP

set_option linter.unusedSectionVars false

open scoped Classical

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm Set Filter Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (K : Type) [Field K] [NumberField K]

scoped instance finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _

scoped instance finBorelSpace : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩

scoped instance : (νf K).IsAddHaarMeasure := by unfold νf; infer_instance

scoped instance : IsFiniteMeasure (μ' K) := by
  unfold μ'
  haveI : IsFiniteMeasure ((μA K).restrict (adelicBox K)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact μA_box_lt_top K⟩
  exact Measure.isFiniteMeasure_map _ _

scoped instance : IsFiniteMeasure ((volume : Measure (MS K)).restrict (FD K)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_FD_lt_top K⟩

scoped instance : IsFiniteMeasure ((νf K).restrict (O K)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact νf_O_lt_top K⟩

scoped instance : IsFiniteMeasure (P K) := by unfold P; infer_instance

def ℓ : MS K →L[ℝ] ℝ := -LinearMap.toContinuousLinearMap (Algebra.trace ℝ (MS K))

end WhitIBP
end
end P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
