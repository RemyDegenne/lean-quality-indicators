namespace OAI

section

section

open Set Filter MeasureTheory ProbabilityTheory Complex

open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem boundary_comparison_failure_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ β x r δ : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hr : 0 < r)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (heq : -(2-4*δ)-2+κ*(β+1)/2=0) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤
      ENNReal.ofReal ((r/(δ*x))^β) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  apply (measure_mono_ae (show {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤ᵐ[P]
      {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*C t ω) x r δ} from ?_)).trans
      (boundary_comparison_failure_probability_regular hC hCc κ β x r δ hκ hx hr hδ hδ2 hβ heq)
  filter_upwards [hCB] with ω he
  intro h
  change BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ at h
  simpa only [he] using h

end SLEExactGauge
end
end
end OAI
