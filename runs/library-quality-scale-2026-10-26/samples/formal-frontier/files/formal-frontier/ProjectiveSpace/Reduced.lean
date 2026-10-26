/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChartScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.LocalProperties.Reduced

set_option warningAsError true

/-!
# Reducedness of projective spectra

This file proves that the projective spectrum of a reduced commutative graded
ring is reduced. It also retains the polynomial-projective-space specialization
through the smaller standard-coordinate cover.
-/

public section

noncomputable section

open AlgebraicGeometry

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

section General

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsReduced A]

/-- The projective spectrum of a reduced commutative graded ring is reduced.

This includes empty projective spectra and the zero ring. -/
instance proj_isReduced :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Proj 𝒜) := by
  refine @AlgebraicGeometry.IsReduced.of_openCover _
    (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover ?_
  intro i
  let _ : IsReduced (HomogeneousLocalization.Away 𝒜 (i.2 : A)) :=
    isReduced_of_injective
      (algebraMap (HomogeneousLocalization.Away 𝒜 (i.2 : A))
        (Localization.Away (i.2 : A)))
      (HomogeneousLocalization.val_injective (𝒜 := 𝒜)
        (x := Submonoid.powers (i.2 : A)))
  change AlgebraicGeometry.IsReduced
    (AlgebraicGeometry.Spec ↧(HomogeneousLocalization.Away 𝒜 (i.2 : A)))
  infer_instance

end General

section Polynomial

variable (R : Type u) [CommRing R] [IsReduced R]
variable (ι : Type v) [Finite ι]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- Polynomial projective space over a reduced commutative ring is reduced.

This includes the empty coordinate type and the zero ring. -/
instance polynomialProj_isReduced :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Proj 𝒜) := by
  let _ := Fintype.ofFinite ι
  refine @AlgebraicGeometry.IsReduced.of_openCover _
    (standardCoordinateAffineOpenCover R ι).openCover ?_
  intro i
  change AlgebraicGeometry.IsReduced
    (AlgebraicGeometry.Spec
      (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)))
  infer_instance

end Polynomial

end ProjectiveSpace
