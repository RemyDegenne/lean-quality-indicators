@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

/-- Applying global sections to the opposite affine coequalizer fork gives a
fork of commutative rings. -/
def quotientRingFork :
    Fork (AffineScheme.Γ.map s.op) (AffineScheme.Γ.map t.op) :=
  Fork.ofι (AffineScheme.Γ.map (coequalizer.π s t).op) (by
    simp only [← AffineScheme.Γ.map_comp]
    rw [← op_comp, ← op_comp, coequalizer.condition])

end AlgebraicGeometry.AffineRelationQuotient
end
end
