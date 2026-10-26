/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChart

/-!
# Localizing a standard chart by a homogeneous polynomial

This file identifies the localization of a polynomial standard chart at the
dehomogenization of a homogeneous polynomial with the degree-zero homogeneous
localization at the product of the chart coordinate and that polynomial.

The construction works over an arbitrary commutative base ring, including the
zero ring, and does not require the homogeneous polynomial to be nonzero or
regular.
-/

public section

noncomputable section

open HomogeneousLocalization
open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type v) (i : ι)

/-- Classical coordinate equality decision, scoped locally to this module. -/
local instance homogeneousPolynomialChartLocalizationDecidableEq : DecidableEq ι :=
  Classical.decEq ι

local notation "Others" => {j : ι // j ≠ i}
local notation "Poly" => MvPolynomial ι R
local notation "Q" => MvPolynomial Others R
local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "Xi" => (MvPolynomial.X i : Poly)

/-- The common degree-zero homogeneous localization obtained from the `i`th
standard chart by additionally inverting a homogeneous polynomial. -/
abbrev StandardChartHomogeneousLocalization {d : ℕ} (F : 𝒜 d) :=
  Away 𝒜 (Xi * (F : Poly))

/-- Restriction from the `i`th standard chart to the common homogeneous
localization at `X i * F`. -/
def standardChartHomogeneousLocalizationMap {d : ℕ} (F : 𝒜 d) :
    StandardChart R ι i →+* StandardChartHomogeneousLocalization R ι i F :=
  HomogeneousLocalization.awayMap 𝒜
    (f := Xi) (x := Xi * (F : Poly)) F.property rfl

/-- The algebra structure induced by restriction from the standard chart. -/
instance standardChartHomogeneousLocalizationAlgebra {d : ℕ} (F : 𝒜 d) :
    Algebra (StandardChart R ι i)
      (StandardChartHomogeneousLocalization R ι i F) :=
  (standardChartHomogeneousLocalizationMap R ι i F).toAlgebra

/-- The coefficient-ring algebra structure on the common homogeneous
localization, induced through the standard chart. -/
instance standardChartHomogeneousLocalizationBaseAlgebra {d : ℕ} (F : 𝒜 d) :
    Algebra R (StandardChartHomogeneousLocalization R ι i F) :=
  ((standardChartHomogeneousLocalizationMap R ι i F).comp
    (algebraMap R (StandardChart R ι i))).toAlgebra

/-- The common homogeneous localization is obtained from the standard chart by
inverting the degree-zero fraction `F / X i ^ d`. -/
theorem isLocalization_standardChartHomogeneousLocalization {d : ℕ}
    (F : 𝒜 d) :
    IsLocalization.Away
      (homogeneousPolynomialOnChart R ι i (F : Poly) F.property)
      (StandardChartHomogeneousLocalization R ι i F) := by
  have hF : homogeneousPolynomialOnChart R ι i (F : Poly) F.property =
      Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R i) F.property := by
    apply HomogeneousLocalization.val_injective
    simp [homogeneousPolynomialOnChart, Away.isLocalizationElem]
  rw [hF]
  exact Away.isLocalization_mul (MvPolynomial.isHomogeneous_X R i)
    F.property rfl (by norm_num)

attribute [instance] isLocalization_standardChartHomogeneousLocalization

/-- The polynomial presentation obtained by localizing the `i`th standard
chart at the dehomogenization of `F`. -/
abbrev StandardChartPolynomialLocalization [Fintype ι] {d : ℕ} (F : 𝒜 d) :=
  Localization.Away
    (dehomogenizedPolynomial R ι i (F : Poly) F.property)

private theorem standardChartEquiv_map_powers_dehomogenizedPolynomial
    [Fintype ι] {d : ℕ} (F : 𝒜 d) :
    Submonoid.map (standardChartEquiv R ι i).toRingEquiv.toMonoidHom
        (Submonoid.powers
          (dehomogenizedPolynomial R ι i (F : Poly) F.property)) =
      Submonoid.powers
        (homogeneousPolynomialOnChart R ι i (F : Poly) F.property) := by
  rw [Submonoid.map_powers]
  congr 1
  exact standardChartEquiv_dehomogenizedPolynomial R ι i (F : Poly) F.property

/-- Localizing the polynomial standard chart at the dehomogenization of `F`
agrees with the common degree-zero homogeneous localization at `X i * F`. -/
@[expose] noncomputable def standardChartPolynomialLocalizationEquiv [Fintype ι]
    {d : ℕ} (F : 𝒜 d) :
    StandardChartPolynomialLocalization R ι i F ≃ₐ[R]
      StandardChartHomogeneousLocalization R ι i F where
  __ := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (dehomogenizedPolynomial R ι i (F : Poly) F.property))
    (T := Submonoid.powers
      (homogeneousPolynomialOnChart R ι i (F : Poly) F.property))
    (StandardChartPolynomialLocalization R ι i F)
    (StandardChartHomogeneousLocalization R ι i F)
    (standardChartEquiv R ι i).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      congr 1
      exact standardChartEquiv_dehomogenizedPolynomial R ι i (F : Poly) F.property)
  commutes' r := by
    change IsLocalization.ringEquivOfRingEquiv
        (M := Submonoid.powers
          (dehomogenizedPolynomial R ι i (F : Poly) F.property))
        (T := Submonoid.powers
          (homogeneousPolynomialOnChart R ι i (F : Poly) F.property))
        (StandardChartPolynomialLocalization R ι i F)
        (StandardChartHomogeneousLocalization R ι i F)
        (standardChartEquiv R ι i).toRingEquiv
        (standardChartEquiv_map_powers_dehomogenizedPolynomial R ι i F)
        (algebraMap Q (StandardChartPolynomialLocalization R ι i F)
          (MvPolynomial.C r)) =
      standardChartHomogeneousLocalizationMap R ι i F
        (algebraMap R (StandardChart R ι i) r)
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    congr 1
    exact (standardChartEquiv R ι i).commutes r

private def standardChartPolynomialLocalizationEquiv_privateConstruction [Fintype ι]
    {d : ℕ} (F : 𝒜 d) :
    StandardChartPolynomialLocalization R ι i F ≃ₐ[R]
      StandardChartHomogeneousLocalization R ι i F where
  __ := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (dehomogenizedPolynomial R ι i (F : Poly) F.property))
    (T := Submonoid.powers
      (homogeneousPolynomialOnChart R ι i (F : Poly) F.property))
    (StandardChartPolynomialLocalization R ι i F)
    (StandardChartHomogeneousLocalization R ι i F)
    (standardChartEquiv R ι i).toRingEquiv
    (standardChartEquiv_map_powers_dehomogenizedPolynomial R ι i F)
  commutes' r := by
    change IsLocalization.ringEquivOfRingEquiv
        (M := Submonoid.powers
          (dehomogenizedPolynomial R ι i (F : Poly) F.property))
        (T := Submonoid.powers
          (homogeneousPolynomialOnChart R ι i (F : Poly) F.property))
        (StandardChartPolynomialLocalization R ι i F)
        (StandardChartHomogeneousLocalization R ι i F)
        (standardChartEquiv R ι i).toRingEquiv
        (standardChartEquiv_map_powers_dehomogenizedPolynomial R ι i F)
        (algebraMap Q (StandardChartPolynomialLocalization R ι i F)
          (MvPolynomial.C r)) =
      standardChartHomogeneousLocalizationMap R ι i F
        (algebraMap R (StandardChart R ι i) r)
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    congr 1
    exact (standardChartEquiv R ι i).commutes r

private theorem standardChartPolynomialLocalizationEquiv_eq_privateConstruction [Fintype ι]
    {d : ℕ} (F : 𝒜 d) :
    standardChartPolynomialLocalizationEquiv R ι i F =
      standardChartPolynomialLocalizationEquiv_privateConstruction R ι i F := rfl

/-- The localization equivalence intertwines the polynomial localization map
with restriction from the homogeneous standard chart. -/
theorem standardChartPolynomialLocalizationEquiv_algebraMap [Fintype ι]
    {d : ℕ} (F : 𝒜 d) (f : Q) :
    standardChartPolynomialLocalizationEquiv R ι i F
        (algebraMap Q (StandardChartPolynomialLocalization R ι i F) f) =
      standardChartHomogeneousLocalizationMap R ι i F
        (standardChartEquiv R ι i f) := by
  change IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers
        (dehomogenizedPolynomial R ι i (F : Poly) F.property))
      (T := Submonoid.powers
        (homogeneousPolynomialOnChart R ι i (F : Poly) F.property))
      (StandardChartPolynomialLocalization R ι i F)
      (StandardChartHomogeneousLocalization R ι i F)
      (standardChartEquiv R ι i).toRingEquiv
      (standardChartEquiv_map_powers_dehomogenizedPolynomial R ι i F)
      (algebraMap Q (StandardChartPolynomialLocalization R ι i F) f) =
    algebraMap (StandardChart R ι i)
      (StandardChartHomogeneousLocalization R ι i F)
      (standardChartEquiv R ι i f)
  apply IsLocalization.ringEquivOfRingEquiv_eq

end ProjectiveSpace
