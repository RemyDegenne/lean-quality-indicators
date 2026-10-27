public section

noncomputable section

open AlgebraicGeometry CategoryTheory

scoped[ProjectiveSpace] attribute [instance] MvPolynomial.gradedAlgebra

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]

variable (ι : Type v)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- The spectrum of the polynomial coordinates on the `i`th standard chart
is canonically isomorphic to the spectrum of its degree-zero homogeneous
localization. -/
@[expose] noncomputable def standardCoordinateChartIso [Fintype ι] (i : ι) :
  AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (StandardChart R ι i)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (standardChartEquiv R ι i).toRingEquiv.toCommRingCatIso.symm.op

end ProjectiveSpace
end
end
