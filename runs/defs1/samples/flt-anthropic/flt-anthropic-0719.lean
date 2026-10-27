namespace P2MW.S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous

set_option autoImplicit false

open MeasureTheory

open scoped ComplexConjugate InnerProductSpace

namespace AvgOp

variable {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
  [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : C →* (H →L[ℂ] H)) (B : ℝ) (hSb : ∀ c : C, ‖S c‖ ≤ B) (hSc : ∀ v : H, Continuous fun c : C => S c v)
  (w : C → ℂ) (hw : Continuous w)

include hSb hSc hw

noncomputable def avg : H →L[ℂ] H :=
  (avgLin μ S B hSb hSc w hw).mkContinuousOfExistsBound (by
    obtain ⟨M, hM⟩ := exists_bound_w S B hSb hSc w hw
    exact ⟨M * B, fun v => norm_integral_le μ S B hSb hSc w hw M hM v⟩)

end AvgOp
end P2MW.S_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
