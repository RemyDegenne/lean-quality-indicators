public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

variable {R : Type u} [CommRing R] (n : ℕ)

variable (I : HopfIdeal R (coordinateHopfAlgebra R n))

/-- The quotient coordinate Hopf algebra represents the matrix point subgroup functor cut out by
the Hopf ideal. -/
def hopfIdealPointsSubgroupNatIso :
    HopfAlgebra.pointsFunctor
        (R := R) (H := CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) ≅
      hopfIdealPointsSubgroupFunctor n I :=
  NatIso.ofComponents
    (fun A ↦ ((hopfIdealPointsSubgroupMulEquiv n I A).trans
      (MulEquiv.ulift.symm : _ ≃* ULift.{u, w} (hopfIdealPointsSubgroup n I A))).toGrpIso)
    (by
      intro A B f
      ext q
      apply ULift.ext
      exact hopfIdealPointsSubgroupMulEquiv_mapPoints n I f q)

end
end TauCeti.GeneralLinear
end
