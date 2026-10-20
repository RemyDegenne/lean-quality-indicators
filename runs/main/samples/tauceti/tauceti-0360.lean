public section

open Bundle FiberBundle MeasureTheory Riemannian.Tensor Set

open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

theorem chartRiemannianVolume_pos_of_isOpen_subset_source
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (α : M)
    {s : Set M} (hs : IsOpen s) (hsub : s ⊆ (chartAt H α).source) (hne : s.Nonempty) :
    0 < chartRiemannianVolume (I := I) α s := by
  let e := extChartAt I α
  let d := chartVolumeDensityData (I := I) α
  have hsub' : s ⊆ e.source := by
    simpa only [e, extChartAt_source] using hsub
  have hmeasure : 0 < (Module.finBasis ℝ E).addHaar (e '' s) :=
    by
      rw [e.image_eq_target_inter_inv_preimage hsub']
      apply Measure.measure_pos_of_nonempty_interior
      obtain ⟨z, hz⟩ := hne
      refine Set.Nonempty.of_closure ⟨e z, ?_⟩
      simpa only [inter_comm] using
        (extChartAt_mem_closure_interior (I := I) (x₀ := α)
          (subset_closure (mem_interior_iff_mem_nhds.mpr (hs.mem_nhds hz))) (hsub' hz))
  rw [chartRiemannianVolume_apply α hs.measurableSet]
  have himage : e '' (s ∩ e.source) = e '' s := by
    rw [inter_eq_left.mpr hsub']
  rw [himage]
  have himage_measurable : MeasurableSet (e '' s) := by
    rw [← himage]
    simpa only [e, inter_comm] using hs.measurableSet_image_extChartAt_source_inter α
  have heq :
      (∫⁻ y in e '' s,
          ENNReal.ofReal (chartVolumeDensity (I := I) α (e.symm y))
            ∂(Module.finBasis ℝ E).addHaar) =
        ∫⁻ y in e '' s, d.toFun y ∂(Module.finBasis ℝ E).addHaar := by
    apply setLIntegral_congr_fun himage_measurable
    rintro y ⟨z, hz, rfl⟩
    exact (d.eq_on_target (e.map_source (hsub' hz))).symm
  rw [heq, setLIntegral_pos_iff d.measurable_toFun]
  have hsupport : e '' s ⊆ Function.support d.toFun := by
    rintro y ⟨z, hz, rfl⟩
    apply Function.mem_support.mpr
    rw [d.eq_on_target (e.map_source (hsub' hz))]
    have hinv : (extChartAt I α).symm (e z) = z := e.left_inv (hsub' hz)
    exact (ENNReal.ofReal_pos.mpr (chartVolumeDensity_pos α (by
      rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I α]
      rw [hinv]
      exact hsub' hz))).ne'
  rw [inter_eq_right.mpr hsupport]
  exact hmeasure

end TauCeti
end
end
