/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveSpace.GradedProjIso
public import GradedRings.SymmetricAlgebra

/-!
# `Proj` of a symmetric algebra in polynomial coordinates

A basis presents a symmetric algebra as a multivariable polynomial ring. The
accepted graded presentation preserves every exact degree in both directions,
so `ProjectiveSpace.GradedProjIso` transports `Proj` and its closed points
across it.

Point and closed-point transport permits independent carrier universes. The
scheme-isomorphism specializations require their two module or module/index
carriers to share a universe, exactly as required by the current `Proj.map`;
the coefficient ring remains universe-independent.
-/

set_option warningAsError true

public section

open AlgebraicGeometry

namespace ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]

section LinearEquiv

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The graded symmetric-algebra map of a linear equivalence followed by that
of its inverse is the identity. -/
theorem symmetricAlgebraGradedMap_comp_symm (e : M ≃ₗ[R] N) :
    (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom.comp
      (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom =
        GradedRingHom.id
          (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N)) := by
  apply GradedRingHom.ext
  intro x
  change SymmetricAlgebra.map e.toLinearMap
    (SymmetricAlgebra.map e.symm.toLinearMap x) = x
  exact (SymmetricAlgebra.congr e).apply_symm_apply x

/-- The graded symmetric-algebra map of the inverse followed by the original
linear equivalence is the identity. -/
theorem symmetricAlgebraGradedMap_symm_comp (e : M ≃ₗ[R] N) :
    (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom.comp
      (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom =
        GradedRingHom.id
          (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) := by
  apply GradedRingHom.ext
  intro x
  change SymmetricAlgebra.map e.symm.toLinearMap
    (SymmetricAlgebra.map e.toLinearMap x) = x
  exact (SymmetricAlgebra.congr e).symm_apply_apply x

/-- A linear equivalence induces the contravariant equivalence on points of
`Proj` of the corresponding symmetric algebras. -/
@[expose] noncomputable def symmetricAlgebraProjectiveSpectrumEquivOfLinearEquiv
    (e : M ≃ₗ[R] N) :
    ProjectiveSpectrum
        (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N)) ≃
      ProjectiveSpectrum
        (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) :=
  projectiveSpectrumEquivOfInverseGradedRingHom
    (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
    (ℬ := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))
    (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
    (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
    (symmetricAlgebraGradedMap_comp_symm e)
    (symmetricAlgebraGradedMap_symm_comp e)

@[simp]
theorem symmetricAlgebraProjectiveSpectrumEquivOfLinearEquiv_apply
    (e : M ≃ₗ[R] N)
    (p : ProjectiveSpectrum
      (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))) :
    symmetricAlgebraProjectiveSpectrumEquivOfLinearEquiv e p =
      ProjectiveSpectrum.comapFun
        (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
        (irrelevant_le_map_of_comp_eq_id
          (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
          (ℬ := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))
          (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
          (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
          (symmetricAlgebraGradedMap_comp_symm e)) p :=
  rfl

/-- A linear equivalence induces the contravariant equivalence on closed
points of `Proj` of the corresponding symmetric algebras. -/
@[expose] noncomputable def symmetricAlgebraProjClosedPointsEquivOfLinearEquiv
    (e : M ≃ₗ[R] N) :
    closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))) ≃
      closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))) :=
  projClosedPointsEquivOfInverseGradedRingHom
    (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
    (ℬ := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))
    (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
    (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
    (symmetricAlgebraGradedMap_comp_symm e)
    (symmetricAlgebraGradedMap_symm_comp e)

@[simp]
theorem symmetricAlgebraProjClosedPointsEquivOfLinearEquiv_apply_coe
    (e : M ≃ₗ[R] N)
    (p : closedPoints
      (Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N)))) :
    (symmetricAlgebraProjClosedPointsEquivOfLinearEquiv e p).1 =
      ProjectiveSpectrum.comapFun
        (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
        (irrelevant_le_map_of_comp_eq_id
          (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
          (ℬ := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N))
          (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
          (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
          (symmetricAlgebraGradedMap_comp_symm e)) p.1 :=
  rfl

end LinearEquiv

section LinearEquivScheme

variable {N : Type v} [AddCommGroup N] [Module R N]

/-- A linear equivalence between modules in a common universe induces the
contravariant scheme isomorphism of `Proj` of their symmetric algebras. The
common module universe is exactly the current boundary of `Proj.map`; the
coefficient ring may live independently. -/
@[expose] noncomputable def symmetricAlgebraProjIsoOfLinearEquiv (e : M ≃ₗ[R] N) :
    Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := N)) ≅
      Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) :=
  projIsoOfInverseGradedRingHom
    (SymmetricAlgebra.gradedMap e.toLinearMap).toGradedRingHom
    (SymmetricAlgebra.gradedMap e.symm.toLinearMap).toGradedRingHom
    (symmetricAlgebraGradedMap_comp_symm e)
    (symmetricAlgebraGradedMap_symm_comp e)

end LinearEquivScheme

variable {I : Type w}

/-- The polynomial presentation after its inverse is the identity graded ring
map. -/
theorem symmetricAlgebraGradedHom_comp_mvPolynomialGradedHom
    (b : Module.Basis I R M) :
    (SymmetricAlgebra.equivMvPolynomialGradedHom b).toGradedRingHom.comp
      (SymmetricAlgebra.equivMvPolynomialSymmGradedHom b).toGradedRingHom =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule I R) := by
  apply GradedRingHom.ext
  intro p
  exact (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply p

/-- The inverse polynomial presentation after the forward presentation is the
identity graded ring map. -/
theorem mvPolynomialGradedHom_comp_symmetricAlgebraGradedHom
    (b : Module.Basis I R M) :
    (SymmetricAlgebra.equivMvPolynomialSymmGradedHom b).toGradedRingHom.comp
      (SymmetricAlgebra.equivMvPolynomialGradedHom b).toGradedRingHom =
        GradedRingHom.id
          (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) := by
  apply GradedRingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x

/-- A basis identifies the closed points of polynomial projective space with
those of the `Proj` of the symmetric algebra, with no common-universe
requirement on the basis index and module. -/
@[expose] noncomputable def mvPolynomialProjClosedPointsEquivSymmetricAlgebra
    (b : Module.Basis I R M) :
    closedPoints (Proj (MvPolynomial.homogeneousSubmodule I R)) ≃
      closedPoints
        (Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))) :=
  projClosedPointsEquivOfInverseGradedRingHom
    (𝒜 := SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M))
    (ℬ := MvPolynomial.homogeneousSubmodule I R)
    (SymmetricAlgebra.equivMvPolynomialGradedHom b).toGradedRingHom
    (SymmetricAlgebra.equivMvPolynomialSymmGradedHom b).toGradedRingHom
    (symmetricAlgebraGradedHom_comp_mvPolynomialGradedHom b)
    (mvPolynomialGradedHom_comp_symmetricAlgebraGradedHom b)

section PolynomialScheme

variable {I : Type v}

/-- A basis whose index and module share a universe identifies polynomial
projective space with the `Proj` of the symmetric algebra. This common
universe is exactly the current scheme-level `Proj.map` boundary. -/
@[expose] noncomputable def mvPolynomialProjIsoSymmetricAlgebra
    (b : Module.Basis I R M) :
    Proj (MvPolynomial.homogeneousSubmodule I R) ≅
      Proj (SymmetricAlgebra.homogeneousSubmodule (R := R) (M := M)) :=
  projIsoOfInverseGradedRingHom
    (SymmetricAlgebra.equivMvPolynomialGradedHom b).toGradedRingHom
    (SymmetricAlgebra.equivMvPolynomialSymmGradedHom b).toGradedRingHom
    (symmetricAlgebraGradedHom_comp_mvPolynomialGradedHom b)
    (mvPolynomialGradedHom_comp_symmetricAlgebraGradedHom b)

end PolynomialScheme


end

end ProjectiveSpace
