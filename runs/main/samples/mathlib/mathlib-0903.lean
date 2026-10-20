@[expose] public section

noncomputable section

open Set Filter ENNReal Finset

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

theorem setToSimpleFunc_eq_sum_filter [DecidablePred fun x ↦ x ≠ (0 : F)]
    {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) :
    setToSimpleFunc T f = ∑ x ∈ f.range with x ≠ 0, T (f ⁻¹' {x}) x := by
  symm
  refine sum_filter_of_ne fun x _ => mt fun hx0 => ?_
  rw [hx0]
  exact map_zero _

end SimpleFunc
end MeasureTheory
end
end
