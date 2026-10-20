public section

open Bundle Manifold Set

open scoped ContDiff Manifold

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n m : ℕ∞ω}

namespace VectorField

variable {V : (x : M) → TangentSpace I x} {s : Set M} {x : M}

theorem mpullbackWithin_extChartAt_symm_apply (V : (x : M) → TangentSpace I x) {y : M}
    (hy : y ∈ (extChartAt I x).source) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
      (extChartAt I x y) =
        (trivializationAt E (TangentSpace I) x (V y)).2 := by
  rw [VectorField.mpullbackWithin_apply, (extChartAt I x).left_inv hy]
  apply (isInvertible_mfderivWithin_extChartAt_symm
    ((extChartAt I x).map_source hy)).inverse_apply_eq.mpr
  have hy' : y ∈ (chartAt H x).source := by simpa only [extChartAt_source] using hy
  rw [← TangentBundle.symmL_trivializationAt hy']
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜)
    (trivializationAt E (TangentSpace I) x)
    (by simpa using hy')]
  exact (Trivialization.symmL_continuousLinearMapAt (R := 𝕜)
    (trivializationAt E (TangentSpace I) x) (by simpa using hy') _).symm

end VectorField
end
end
