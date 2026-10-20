public section

noncomputable section

namespace TauCeti

open Function InnerProductSpace Metric Set Topology

variable {f g : ℂ → ℝ} {Ω : Set ℂ} {a : ℂ}

theorem eqOn_const_of_harmonicOnNhd_of_isLocalMax
    (hΩa : Ω ∈ 𝓝 a) (hΩconn : IsPreconnected Ω) (hf : HarmonicOnNhd f Ω)
    (hmax : IsLocalMax f a) : EqOn f (const ℂ (f a)) Ω := by
  have hΩeventually : ∀ᶠ z in 𝓝 a, z ∈ Ω := hΩa
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hΩeventually.and hmax)
  have hconst : EqOn f (const ℂ (f a)) (ball a r) :=
    eqOn_of_harmonicOnNhd_of_le_of_eq (ball_mem_nhds a hr)
      (convex_ball a r).isPreconnected
      (hf.mono fun _ hz ↦ (hball hz).1) (harmonicOnNhd_const (f a))
      (fun _ hz ↦ (hball hz).2) rfl
  have hfanalytic : AnalyticOnNhd ℝ f Ω := fun z hz ↦ HarmonicAt.analyticAt (hf z hz)
  apply hfanalytic.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hΩconn
    (mem_of_mem_nhds hΩa)
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact hconst hz

end TauCeti
end
end
