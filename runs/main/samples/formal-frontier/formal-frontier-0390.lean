@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace AlgebraicTopology

open Convexity Convexity.StdSimplex

universe u

theorem singularSubdivision_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (c : SingularChainFinsupp X n) :
    singularFinsuppMap f n (singularSubdivision X n c) =
      singularSubdivision Y n (singularFinsuppMap f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x z =>
      have hz : Finsupp.single x z = z • Finsupp.single x 1 := by simp
      rw [hz]
      simp only [map_smul, singularSubdivision_single, singularFinsuppMap_single]
      rw [singularFinsuppMap_realizeAffineChain]

end AlgebraicTopology
end
end
