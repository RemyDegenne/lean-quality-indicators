@[expose] public section

noncomputable section

open TopologicalSpace

open scoped ContDiff Manifold

universe u v w

namespace ChartedSpace

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

/-- Chosen coordinates around a point at arbitrary manifold regularity. -/
def chartLocalBall (n : ℕ∞ω) [IsManifold 𝓘(𝕜, E) n M] (x : M) :
    ChartLocalBall (𝕜 := 𝕜) (E := E) n x := by
  let chart := chartAt E x
  have hexists : ∃ radius > 0, Metric.ball (chart x) radius ⊆ chart.target :=
    Metric.isOpen_iff.mp chart.open_target (chart x) (mem_chart_target E x)
  let radius := Classical.choose hexists
  have hradius : 0 < radius := (Classical.choose_spec hexists).1
  have hball : Metric.ball (chart x) radius ⊆ chart.target :=
    (Classical.choose_spec hexists).2
  let ball : Opens E := chartBall x radius
  have hball_subset : (ball : Set E) ⊆ chart.target := hball
  let neighborhood : Opens M :=
    ⟨chart.source ∩ chart ⁻¹' (ball : Set E),
      chart.isOpen_inter_preimage ball.isOpen⟩
  have hmem : x ∈ neighborhood := by
    exact ⟨mem_chart_source E x, (mem_chartBall x radius (chart x)).2
      (by simpa [chart] using hradius)⟩
  have hsource : (neighborhood : Set M) ⊆ chart.source := Set.inter_subset_left
  have himage : chart '' (neighborhood : Set M) = (ball : Set E) := by
    apply Set.Subset.antisymm
    · rintro targetPoint ⟨point, ⟨-, hballPoint⟩, rfl⟩
      exact hballPoint
    · intro targetPoint hballPoint
      have htarget : targetPoint ∈ chart.target := hball_subset hballPoint
      exact ⟨chart.symm targetPoint, ⟨chart.map_target htarget,
        by simpa only [Set.mem_preimage, chart.right_inv htarget] using hballPoint⟩,
          chart.right_inv htarget⟩
  let homeo : neighborhood ≃ₜ ball :=
    chart.homeomorphOfImageSubsetSource hsource himage
  have hsmooth : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo := by
    intro point
    have hchart : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        chart point.1 :=
      (contMDiffOn_chart (I := 𝓘(𝕜, E)) (x := x) point.1
        (hsource point.2)).contMDiffAt (chart.open_source.mem_nhds (hsource point.2))
    have hrestr : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (fun point : neighborhood => chart point.1) point :=
      contMDiffAt_subtype_iff.mpr hchart
    have htarget : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo) point := by
      convert hrestr using 1
      funext sourcePoint
      rfl
    exact (show ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo) point ↔
          ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo point from
        ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff homeo Set.univ point).mp htarget
  have hsmooth_symm : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo.symm := by
    intro point
    have hchart : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        chart.symm point.1 :=
      (contMDiffOn_chart_symm (I := 𝓘(𝕜, E)) (x := x) point.1
        (hball_subset point.2)).contMDiffAt
          (chart.open_target.mem_nhds (hball_subset point.2))
    have hrestr : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (fun point : ball => chart.symm point.1) point :=
      contMDiffAt_subtype_iff.mpr hchart
    have htarget : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo.symm) point := by
      convert hrestr using 1
      funext targetPoint
      rfl
    exact (show ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
        (Subtype.val ∘ homeo.symm) point ↔
          ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) n homeo.symm point from
        ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff homeo.symm Set.univ point).mp htarget
  exact {
    neighborhood := neighborhood
    mem_neighborhood := hmem
    neighborhood_subset_source := hsource
    radius := radius
    radius_pos := hradius
    coord := { toEquiv := homeo.toEquiv
               contMDiff_toFun := hsmooth
               contMDiff_invFun := hsmooth_symm }
    coord_apply := fun point => rfl
    coord_symm_apply := fun point => rfl }

end ChartedSpace
end
end
