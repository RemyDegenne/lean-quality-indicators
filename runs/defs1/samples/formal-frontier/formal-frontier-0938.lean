@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

section Chart

variable (LQ : Type s) [CommRing LQ]
  [Algebra (CoordinateRing A) LQ] [Algebra A LQ]
  [IsScalarTower A (CoordinateRing A) LQ] [IsLocalization.Away (w A) LQ]

variable (LB : Type t) [CommRing LB]
  [Algebra (ParameterPolynomial A) LB] [Algebra A LB]
  [IsScalarTower A (ParameterPolynomial A) LB] [IsLocalization.Away (W A) LB]

/-- The chart equivalence, using the inverse identities and explicit morphisms. -/
noncomputable def chartEquiv : LQ ≃ₐ[A] LB :=
  AlgEquiv.ofAlgHom (chartForward A LQ LB) (chartBackward A LQ LB)
    (chartForward_comp_chartBackward A LQ LB) (chartBackward_comp_chartForward A LQ LB)

end Chart
end SplitQuadric
end
end
