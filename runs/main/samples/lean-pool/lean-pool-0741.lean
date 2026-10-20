@[expose] public section

open Filter Set OpenPartialHomeomorph Metric

open scoped ContDiff Manifold Topology

namespace RS

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z]

section Composition

theorem multiplicityENat_comp {G : Y → Z} {F : X → Y} {x : X}
    (hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (F x)) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat (G ∘ F) x = multiplicityENat G (F x) * multiplicityENat F x := by
  obtain ⟨hFc, hFa⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF
  obtain ⟨-, hGa⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hG
  have hxc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hxc' : F x ∈ (chartAt ℂ (F x)).source := mem_chart_source ℂ (F x)
  -- the uncentered composite of `F` in the standard charts
  set g : ℂ → ℂ := fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) with hg_def
  have hg : AnalyticAt ℂ g (chartAt ℂ x x) := analyticAt_inChartAt_iff.mp hFa
  have hgz₀ : g (chartAt ℂ x x) = chartAt ℂ (F x) (F x) := by
    rw [hg_def]
    simp only
    rw [(chartAt ℂ x).left_inv hxc]
  -- the middle charts cancel on a neighborhood of the base point
  have hev : inChartAt (G ∘ F) x =ᶠ[𝓝 (chartAt ℂ x x)] (inChartAt G (F x)) ∘ g := by
    have hcF : ContinuousAt (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
      apply ContinuousAt.comp ?_
        ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxc))
      rw [(chartAt ℂ x).left_inv hxc]
      exact hFc
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ x x),
        F ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (F x)).source := by
      apply hcF.preimage_mem_nhds
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).left_inv hxc]
      exact (chartAt ℂ (F x)).open_source.mem_nhds hxc'
    filter_upwards [h2] with z h2z
    simp only [inChartAt, Function.comp_apply, hg_def]
    rw [(chartAt ℂ (F x)).left_inv h2z]
  calc multiplicityENat (G ∘ F) x
      = analyticOrderAt ((inChartAt G (F x)) ∘ g) (chartAt ℂ x x) :=
        analyticOrderAt_congr hev
    _ = analyticOrderAt (inChartAt G (F x)) (g (chartAt ℂ x x))
          * analyticOrderAt (fun z ↦ g z - g (chartAt ℂ x x)) (chartAt ℂ x x) := by
        refine AnalyticAt.analyticOrderAt_comp ?_ hg
        rw [hgz₀]
        exact hGa
    _ = multiplicityENat G (F x) * multiplicityENat F x := by
        congr 1
        · rw [hgz₀, multiplicityENat_def]
        · rw [multiplicityENat_def]
          apply analyticOrderAt_congr
          apply Eventually.of_forall
          intro z
          rw [hgz₀]
          simp only [inChartAt, hg_def]

end Composition
end RS
end
