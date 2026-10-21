namespace OAI

noncomputable section

section

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory

open scoped ContDiff Matrix.Norms.Elementwise

namespace ThreeManifold.CompactMetric

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma framed_unit_entry_zero_index (right : Bool) {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (h0 : γ 0 0 = 0) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  obtain ⟨p,hp⟩ := framed_closed_momentum right hδ hU hγ hL.le hsub hrc
  by_cases hc : ∃ c ∈ Ioo 0 L, deriv γ c 0 = 0
  · obtain ⟨c,hc,hvc⟩ := hc
    exact framed_turn_index right hδ hC hsmall (hB right) hU hsub hc hγ hJ hp h0 hrc hend hvc hr hunit
  · exact framed_monotone_index right hδ hU hL hsub hγ hJ hp hrc hr
      (Or.inl (Or.inl h0)) hend (fun s hs hzero => hc ⟨s,hs,hzero⟩) hunit

end ThreeManifold.CompactMetric
end
end
end OAI
