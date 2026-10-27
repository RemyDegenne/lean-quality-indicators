@[expose] public section

open MeasureTheory NNReal ENNReal Complex

open TopologicalSpace Measure

noncomputable section

open MeasureTheory.Measure

variable {d : ℕ} [NeZero d]

variable [Fintype (Fin d)]

open scoped SchwartzMap

variable {𝕜 : Type} [RCLike 𝕜]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/--
Compose an Lp function with a continuous linear map.
This should be the canonical way to lift real Lp functions to complex Lp functions.
-/
noncomputable def composedFunction {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ) : Lp ℂ 2 μ :=
  A.compLp f

end
end
