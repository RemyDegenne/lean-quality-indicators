public section

open scoped Topology

open Function Set

open scoped Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ} (t₀ : ℝ) {x₀ : M}

variable {t₀}

theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless [BoundarylessManifold I M]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsMIntegralCurveAt γ v t₀) (hγ' : IsMIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝 t₀] γ' :=
  isMIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h

end
