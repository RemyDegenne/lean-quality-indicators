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

section CoefficientBase

variable (S : Type (max u v)) [CommRing S] (κ : Type v)

local notation "ℬ" => MvPolynomial.homogeneousSubmodule κ S

@[reassoc]
theorem standardCoordinateChartMap_toSpec [Fintype κ] (i : κ) :
    standardCoordinateChartMap S κ i ≫ polynomialProjToSpec S κ =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : S →+* MvPolynomial {j : κ // j ≠ i} S)) := by
  have hcoeff :
      (mvPolynomialDegreeZeroEquiv S κ).toRingEquiv.toCommRingCatIso.hom ≫
          CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom ℬ
            (Submonoid.powers (MvPolynomial.X i))) =
        CommRingCat.ofHom (algebraMap S (StandardChart S κ i)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact fromZeroRingHom_mvPolynomialDegreeZeroEquiv S κ i r
  rw [polynomialProjToSpec_eq_toSpecZero, standardCoordinateChartMap]
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, hcoeff]
  exact standardCoordinateChartIso_hom_toSpec S κ i

end CoefficientBase
end ProjectiveSpace
end
end
