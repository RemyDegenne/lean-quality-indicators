public section

open Bundle FiberBundle VectorField

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold.ContMDiffNondegenerateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetric (I := I) (M := M))
  {cov cov' : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {X Y Z : Π x : M, TangentSpace I x} {x : M}

theorem koszul_add_koszul_swap_last_two :
    g.koszul Z X Y x + g.koszul Z Y X x =
      2 * mvfderiv I (fun y ↦ g y (X y) (Y y)) x (Z x) :=
  TauCeti.Manifold.koszulBilinear_add_koszulBilinear_swap_last_two g.apply_comm

end TauCeti.Manifold.ContMDiffNondegenerateMetric
end
end
