public section

noncomputable section

namespace Subgroup

open Set

open scoped ContDiff Manifold Topology

variable {E H G F F' : Type*} {n : ℕ∞ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [ContMDiffMul I n G]

variable (K : Subgroup G) (e : OpenPartialHomeomorph G (F × F'))
  (he : TauCeti.IsSliceChart e ((univ : Set F) ×ˢ ({0} : Set F')) (K : Set G))
  (h1 : (1 : G) ∈ e.source)
  (he' : ContMDiffOn I 𝓘(ℝ, F × F') n e e.source)
  (he_symm : ContMDiffOn 𝓘(ℝ, F × F') I n e.symm e.target)

include he' he_symm in
theorem isDiffImmersionAt_subtypeVal_chartedSpaceOfIsSliceChart (hn : 1 ≤ n) (k : K) :
    let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
    let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
    IsDiffImmersionAt 𝓘(ℝ, F) I (fun x : K ↦ (x : G)) k := by
  dsimp only
  let _ : ContinuousMul G := continuousMul_of_contMDiffMul I n
  let _ : ChartedSpace F K := chartedSpaceOfIsSliceChart K e he h1
  let _ : IsManifold 𝓘(ℝ, F) n K :=
    isManifold_chartedSpaceOfIsSliceChart K e he h1 he' he_symm
  have _ : IsManifold I 1 G := IsManifold.of_le hn
  have _ : IsManifold 𝓘(ℝ, F) 1 K := IsManifold.of_le hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hsrc : (k : G)⁻¹ * (k : G) ∈ e.source := by simpa using h1
  -- The tangential coordinate of the ambient chart translated to `k`, as a function on `G`.
  have hr : ContMDiffAt I 𝓘(ℝ, F) n (fun x : G ↦ (e ((k : G)⁻¹ * x)).1) (k : G) :=
    contDiff_fst.contMDiff.contMDiffAt.comp _
      ((he'.contMDiffAt (e.open_source.mem_nhds hsrc)).comp _ contMDiff_mul_left.contMDiffAt)
  have hincl : ContMDiff 𝓘(ℝ, F) I n (fun x : K ↦ (x : G)) :=
    contMDiff_subtypeVal_chartedSpaceOfIsSliceChart K e he h1 he_symm
  -- Restricted to the subgroup it is the preferred subgroup chart at `k`.
  have hcomp : (fun x : G ↦ (e ((k : G)⁻¹ * x)).1) ∘ (fun x : K ↦ (x : G)) =
      ⇑(chartAt F k) := by
    funext x
    rw [chartedSpaceOfIsSliceChart_chartAt K e he h1 k, preferredSliceChart_apply]
    rfl
  refine IsDiffImmersionAt.of_comp (hincl.mdifferentiableAt hn0) (hr.mdifferentiableAt hn0) ?_
  -- A chart has the identity as its differential at its own base point.
  rw [isDiffImmersionAt_iff, hcomp,
    mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source F k)]
  refine ⟨ContinuousLinearMap.id ℝ F, fun v ↦ ?_⟩
  exact tangentCoordChange_self (I := 𝓘(ℝ, F)) (mem_extChartAt_source (I := 𝓘(ℝ, F)) k)

end Subgroup
end
end
