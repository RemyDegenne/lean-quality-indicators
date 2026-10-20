public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

universe v v'

noncomputable section

variable (n : ℕ)

variable (hn : 4 ≤ n)

@[simp]
theorem graphAutPoints_apply_apply (A : Type v) [CommRing A] (g : points n hn A) :
    graphAutPoints n hn A (graphAutPoints n hn A g) = g := by
  refine Subtype.ext ?_
  rw [coe_graphAutPoints, coe_graphAutPoints]
  have hgroup : graphAutMatrix n hn A * (graphAutMatrix n hn A * (g : _) *
        (graphAutMatrix n hn A)⁻¹) * (graphAutMatrix n hn A)⁻¹ =
      (graphAutMatrix n hn A * graphAutMatrix n hn A) * (g : _) *
        (graphAutMatrix n hn A * graphAutMatrix n hn A)⁻¹ := by
    group
  rw [hgroup, graphAutMatrix_mul_self, inv_neg, inv_one, neg_one_mul, mul_neg, mul_one,
    neg_neg]

end
end TauCeti.TypeDSpinCarrier
end
