public section

open MeasureTheory Function Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}

theorem ConcaveOn.condExp_map_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_univ hm hφ_cont.neg hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]

end
