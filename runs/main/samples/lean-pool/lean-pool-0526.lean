@[expose] public section

open scoped ContDiff Manifold

open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MFormData

theorem resAt_eq_of_mem_source {θ : MFormData X} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    θ.resAt x = RS.resAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
      θ.coeffAt x (chartAt ℂ x (e.symm z))) (e x) := by
  obtain ⟨hτ, hτ'⟩ := analyticAt_transition he (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x)
  have hφ₀ : (⇑(chartAt ℂ x) ∘ ⇑e.symm) (e x) = chartAt ℂ x x := by
    simp only [Function.comp_apply]; rw [e.left_inv hx]
  have hf : MeromorphicAt (θ.coeffAt x) (chartAt ℂ x x) := θ.meromorphicAt_coeffAt x
  have hkey := resAt_comp_mul_deriv hτ hτ' hφ₀ hf
  have hfun : (fun w => θ.coeffAt x ((⇑(chartAt ℂ x) ∘ ⇑e.symm) w) *
        deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) w) =
      (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z * θ.coeffAt x (chartAt ℂ x (e.symm z))) := by
    funext w; rw [Function.comp_apply]; ring
  rw [hfun] at hkey
  exact hkey.symm

end MFormData
end RS
end
end
