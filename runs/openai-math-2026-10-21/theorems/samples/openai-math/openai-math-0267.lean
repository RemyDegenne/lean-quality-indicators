namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators

universe uB uR uIota uKappa

namespace ExactModuli.KW

section Normalize

variable {B : Type uB} [MeasurableSpace B] {μ : Measure B}

lemma oldCombination_ae (x : Lp ℝ 1 μ) {κ : Type uKappa} [Fintype κ]
    (u : κ → Lp ℝ 1 μ) (c : κ → ℝ) :
    (x + ∑ k, c k • u k : Lp ℝ 1 μ) =ᵐ[μ] oldCombination x (fun k => (u k : B → ℝ)) c := by
  filter_upwards [Lp.coeFn_add x (∑ k, c k • u k), coeFn_L1_smul_sum c u] with b hb hb'
  simpa only [Pi.add_apply, hb', oldCombination] using hb

end Normalize
end ExactModuli.KW
end
end OAI
