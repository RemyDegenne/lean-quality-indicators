namespace OAI

noncomputable section

open Bundle Set Filter

open scoped Manifold Bundle Topology BoundedContinuousFunction

open scoped Topology

open Set Filter

namespace QuotientLift

lemma twice_dslope_differentiable (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope (dslope f 0) 0) := by
  rw [← differentiableOn_univ]
  apply (Complex.differentiableOn_dslope (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 0)).2
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hf.differentiableOn

end QuotientLift
end
end OAI
