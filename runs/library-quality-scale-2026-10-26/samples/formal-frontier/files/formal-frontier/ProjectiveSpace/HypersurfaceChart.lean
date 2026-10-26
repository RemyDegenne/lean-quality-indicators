/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChart

/-!
# Homogeneous hypersurfaces on standard projective charts

This file descends the polynomial transition between two standard projective
charts to the corresponding localized hypersurface coordinate rings. The
construction works for a homogeneous polynomial over an arbitrary commutative
base ring, including the zero ring.
-/

public section

noncomputable section

open HomogeneousLocalization
open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R]
variable (ι : Type v) (i : ι)

/-- Classical equality decision for the coordinate type, local to this module. -/
local instance instDecidableEqHypersurfaceCoordinates : DecidableEq ι := Classical.decEq ι

local notation "Others" => {j : ι // j ≠ i}
local notation "Poly" => MvPolynomial ι R
local notation "Q" => MvPolynomial Others R
local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- The dehomogenized equation from the `i`th chart, restricted to the
`i,j` polynomial overlap. -/
@[expose] def localizedDehomogenizedPolynomial [Fintype ι] (j : Others) {d : ℕ}
    (F : Poly) (hF : F ∈ 𝒜 d) :
    StandardChartPolynomialOverlap R ι i j :=
  algebraMap Q (StandardChartPolynomialOverlap R ι i j)
    (dehomogenizedPolynomial R ι i F hF)

/-- The dehomogenized equation from the `j`th chart, restricted to the same
overlap in its right polynomial presentation. -/
@[expose] def localizedDehomogenizedPolynomialRight [Fintype ι] (j : Others) {d : ℕ}
    (F : Poly) (hF : F ∈ 𝒜 d) :
    StandardChartPolynomialOverlapRight R ι i j :=
  algebraMap (MvPolynomial {k : ι // k ≠ j.1} R)
    (StandardChartPolynomialOverlapRight R ι i j)
    (dehomogenizedPolynomial R ι j.1 F hF)

/-- Under the left polynomial-overlap presentation, the localized
dehomogenized equation is the restriction of `F / X i ^ d`. -/
theorem standardChartPolynomialOverlapEquiv_localizedDehomogenizedPolynomial
    [Fintype ι] (j : Others) {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) :
    standardChartPolynomialOverlapEquiv R ι i j
        (localizedDehomogenizedPolynomial R ι i j F hF) =
      standardChartOverlapMap R ι i j
        (homogeneousPolynomialOnChart R ι i F hF) := by
  rw [localizedDehomogenizedPolynomial,
    standardChartPolynomialOverlapEquiv_algebraMap,
    standardChartEquiv_dehomogenizedPolynomial]

/-- Under the right polynomial-overlap presentation, the localized
dehomogenized equation is the restriction of `F / X j ^ d`. -/
theorem standardChartPolynomialOverlapEquivRight_localizedDehomogenizedPolynomial
    [Fintype ι] (j : Others) {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) :
    standardChartPolynomialOverlapEquivRight R ι i j
        (localizedDehomogenizedPolynomialRight R ι i j F hF) =
      standardChartOverlapMapRight R ι i j
        (homogeneousPolynomialOnChart R ι j.1 F hF) := by
  rw [localizedDehomogenizedPolynomialRight]
  rw [standardChartPolynomialOverlapEquivRight_algebraMap,
    standardChartEquiv_dehomogenizedPolynomial]

/-- The two chart representatives of a homogeneous polynomial differ on an
overlap by the expected power of the invertible transition coordinate. -/
theorem homogeneousPolynomialOnChart_overlap (j : Others) {d : ℕ} (F : Poly)
    (hF : F ∈ 𝒜 d) :
    standardChartOverlapMap R ι i j
        (homogeneousPolynomialOnChart R ι i F hF) =
      standardChartOverlapMapRight R ι i j
          (homogeneousPolynomialOnChart R ι j.1 F hF) *
        (standardChartOverlapMap R ι i j
          (coordinateRatio R ι i j)) ^ d := by
  rw [show standardChartOverlapMap R ι i j
      (homogeneousPolynomialOnChart R ι i F hF) = _ from by
    simpa [standardChartOverlapMap, homogeneousPolynomialOnChart] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R j.1) rfl d
        (MvPolynomial.isHomogeneous_X R i) F (by simpa using hF))]
  rw [show standardChartOverlapMapRight R ι i j
      (homogeneousPolynomialOnChart R ι j.1 F hF) = _ from by
    simpa [standardChartOverlapMapRight, homogeneousPolynomialOnChart] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R i) (by rw [mul_comm]) d
        (MvPolynomial.isHomogeneous_X R j.1) F (by simpa using hF))]
  rw [show standardChartOverlapMap R ι i j
      (coordinateRatio R ι i j) = _ from by
    simpa [standardChartOverlapMap, coordinateRatio] using
      (HomogeneousLocalization.awayMap_mk 𝒜
        (MvPolynomial.isHomogeneous_X R j.1) rfl 1
        (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.X j.1)
        (by simpa using MvPolynomial.isHomogeneous_X R j.1))]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    Localization.mk_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The polynomial transition carries the `i`th dehomogenized equation to the
`j`th equation times the expected power of the transition unit. -/
theorem standardChartPolynomialTransition_localizedDehomogenizedPolynomial
    [Fintype ι] (j : Others) {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) :
    standardChartPolynomialTransition R ι i j
        (localizedDehomogenizedPolynomial R ι i j F hF) =
      localizedDehomogenizedPolynomialRight R ι i j F hF *
        standardChartPolynomialTransitionUnit R ι i j ^ d := by
  apply (standardChartPolynomialOverlapEquivRight R ι i j).injective
  rw [map_mul, map_pow]
  simp only [standardChartPolynomialTransition, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply,
    standardChartPolynomialOverlapEquivRight_transitionUnit]
  rw [standardChartPolynomialOverlapEquiv_localizedDehomogenizedPolynomial,
    standardChartPolynomialOverlapEquivRight_localizedDehomogenizedPolynomial]
  exact homogeneousPolynomialOnChart_overlap R ι i j F hF

/-- The standard polynomial transition carries the localized principal ideal
of one dehomogenized equation to that of the other chart. -/
theorem standardChartPolynomialTransition_map_span_dehomogenizedPolynomial
    [Fintype ι] (j : Others) {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) :
    Ideal.map (standardChartPolynomialTransition R ι i j :
        StandardChartPolynomialOverlap R ι i j →+*
          StandardChartPolynomialOverlapRight R ι i j)
        (Ideal.span {localizedDehomogenizedPolynomial R ι i j F hF}) =
      Ideal.span {localizedDehomogenizedPolynomialRight R ι i j F hF} := by
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span
      {standardChartPolynomialTransition R ι i j
        (localizedDehomogenizedPolynomial R ι i j F hF)} = _
  rw [standardChartPolynomialTransition_localizedDehomogenizedPolynomial]
  exact Ideal.span_singleton_mul_right_unit
    ((isUnit_standardChartPolynomialTransitionUnit R ι i j).pow d) _

/-- The two localized affine presentations of a homogeneous hypersurface agree
on a standard-chart overlap. -/
noncomputable def standardChartHypersurfaceOverlapEquiv [Fintype ι]
    (j : Others) {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d) :
    (StandardChartPolynomialOverlap R ι i j ⧸
        Ideal.span {localizedDehomogenizedPolynomial R ι i j F hF}) ≃ₐ[R]
      (StandardChartPolynomialOverlapRight R ι i j ⧸
        Ideal.span {localizedDehomogenizedPolynomialRight R ι i j F hF}) :=
  Ideal.quotientEquivAlg _ _ (standardChartPolynomialTransition R ι i j)
    (standardChartPolynomialTransition_map_span_dehomogenizedPolynomial
      R ι i j F hF).symm

@[simp]
theorem standardChartHypersurfaceOverlapEquiv_mk [Fintype ι]
    (j : Others) {d : ℕ} (F : Poly) (hF : F ∈ 𝒜 d)
    (x : StandardChartPolynomialOverlap R ι i j) :
    standardChartHypersurfaceOverlapEquiv R ι i j F hF
        (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (standardChartPolynomialTransition R ι i j x) := by
  apply Ideal.quotientEquivAlg_mk

end ProjectiveSpace
