public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The affine complex-point chart of a cone, with its monomial-embedding topology. -/
@[expose] noncomputable def analyticAffineChart (σ : Φ.cones) : TopCat :=
  let g := analyticChartGenerators Φ σ
  let _ := affinePointTopology g.2
  TopCat.of (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))

end TauCeti.Toric.Fan
end
