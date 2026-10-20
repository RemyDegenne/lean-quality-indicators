public section

namespace TauCeti.UpperUnitriangular

open Algebra.TensorProduct CategoryTheory WithConv

universe u v w

section HopfAlgebra

variable (R : Type u) [CommRing R] (m : Type v) [Fintype m] [LinearOrder m]

section Functor

/-- The convolution-points functor of the upper-unitriangular coordinate Hopf algebra is
naturally isomorphic to the ordinary upper-unitriangular group functor. -/
noncomputable def pointsNatIso :
    HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) ≅
      upperUnitriangularFunctor (R := R) m :=
  NatIso.ofComponents
    (fun A ↦ ((pointsMulEquiv (R := R) (A := A) m).trans
      MulEquiv.ulift.symm).toGrpIso)
    (by
      intro A B φ
      ext f
      apply ULift.ext
      exact pointsMulEquiv_mapValue R m φ.hom f)

end Functor
end HopfAlgebra
end TauCeti.UpperUnitriangular
end
