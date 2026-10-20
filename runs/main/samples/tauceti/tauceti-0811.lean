public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

theorem Wkp.exists_hasWeakLineDerivOn_value :
    ∀ (k : ℕ) (w : Wkp mu Omega p (k + 1)) (v : E), ∃ d : Wkp mu Omega p k,
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 1) w) (Wkp.value k d) v
  | 0, w, v => by
      refine ⟨(innerSL ℝ v).compLp (Wkp.iteratedGradient 0 w), ?_⟩
      rw [Wkp.value_zero]
      refine ((Wkp.hasWeakFDerivOn_value w).hasWeakLineDerivOn v).congr_ae_deriv ?_
      filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w)] with x hx
      rw [hx, innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]
  | k + 1, w, v => (Wkp.exists_wkp_lineDeriv v k w).imp fun _ h => h.1

end TauCeti
end
end
