public section

open Bundle Manifold Set

open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

variable {p : M}

variable (I) in
include I in
theorem isGeodesicSpace_of_completeSpace [CompleteSpace M] : IsGeodesicSpace M := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  exact ⟨fun x y ↦ exists_isGeodesicSegment_of_expDomain_eq_univ
    (expDomain_eq_univ_of_completeSpace (I := I) x) y⟩

end TauCeti.Manifold
end
