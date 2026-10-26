/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProjectiveSpace.StandardChartScheme
public import SchemeProperties.FactorialNormal

public section

set_option warningAsError true

/-!
# Factoriality and normality of polynomial projective space

This file proves that polynomial projective space over a unique factorization
ring is factorial and hence normal. The proof uses the literal standard affine
cover, whose coordinate rings are multivariable polynomial rings over the base.
-/

noncomputable section

open AlgebraicGeometry

open scoped ProjectiveSpace

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommRing R] [UniqueFactorizationMonoid R]
variable (ι : Type v) [Finite ι]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R

/-- Polynomial projective space over a unique factorization ring is factorial.

This includes the empty coordinate type. -/
instance polynomialProj_isFactorial :
    AlgebraicGeometry.IsFactorial (AlgebraicGeometry.Proj 𝒜) := by
  let _ := Fintype.ofFinite ι
  refine @AlgebraicGeometry.IsFactorial.of_openCover _
    (standardCoordinateAffineOpenCover R ι).openCover ?_
  intro i
  change AlgebraicGeometry.IsFactorial
    (AlgebraicGeometry.Spec
      (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)))
  infer_instance

/-- Polynomial projective space over a unique factorization ring is normal. -/
instance polynomialProj_isNormal :
    AlgebraicGeometry.IsNormal (AlgebraicGeometry.Proj 𝒜) := by
  infer_instance

end ProjectiveSpace
