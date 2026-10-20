public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CompletedGroupAlgebra

/-- Projection from the finite-quotient group-algebra limit to one coordinate
`R[G/U]`. -/
@[expose] def proj (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) (U : OpenNormalSubgroup G) :
    CompletedGroupAlgebra R G →+* MonoidAlgebra R (G ⧸ U.toSubgroup) :=
  (limit.π (finiteQuotientSystem R G) U).hom

end CompletedGroupAlgebra
end
end
