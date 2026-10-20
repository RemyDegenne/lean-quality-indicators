public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

@[simp]
theorem analyticAffineChartDiagram_obj (σ : Φ.cones) :
    (Φ.analyticAffineChartDiagram).obj σ =
      Φ.analyticAffineChart σ :=
  (rfl)

end TauCeti.Toric.Fan
end
