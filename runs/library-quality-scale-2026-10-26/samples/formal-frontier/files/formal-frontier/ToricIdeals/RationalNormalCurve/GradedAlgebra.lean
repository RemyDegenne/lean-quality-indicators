/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ToricIdeals.RationalNormalCurve.HomogeneousBasis
public import ToricIdeals.RationalNormalCurve.Augmentation
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The standard graded algebra of the full Hankel quotient

The homogeneous image submodules of the full Hankel quotient carry its standard
natural-number grading. `quotientHomogeneousGradedAlgebra` combines their internal
direct-sum property with unit and product closure using
`DirectSum.IsInternal.gradedAlgebra`. It retains the quotient's coefficient
algebra structure and the existing homogeneous submodules and bases.

Consumers can use `DirectSum.decomposeAlgEquiv`, `GradedAlgebra.proj`, and
`GradedRing.projZeroRingHom` directly. Homogeneous representatives, membership,
extensionality, coordinates, and basis multiplication are supplied by
`ToricIdeals.RationalNormalCurve.HomogeneousBasis`; no alternative decomposition
or multiplication is introduced here. The degree-zero submodule is the
coefficient image: this follows from `MvPolynomial.homogeneousSubmodule_zero`
and `Submodule.map_one`. The zero projection is coefficient inclusion after
`quotientAugmentation`, as expressed by `quotientHomogeneous_projZeroRingHom`.
Its codomain is the full quotient, whereas augmentation has codomain `R`.

The grading applies over every commutative ring, including zero rings and rings
with nilpotents, and for every parameter `n`. At parameter `n = 0`, the full
quotient is `R[X₀]`: `X₀` has homogeneous degree one, and its zero projection is
zero. The parametrization sending `X₀` to `1` is not used for this grading.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, Exercise
  3.6.F, for the Hankel presentation motivating the coordinate ring.
* Mathlib contributors, `Mathlib.RingTheory.GradedAlgebra.Basic` and
  `Mathlib.Algebra.DirectSum.Decomposition`, for the graded-algebra construction,
  the uniqueness of decomposition on a fixed family, and the degree-zero ring
  homomorphism.
-/

@[expose] public section

namespace ToricIdeals.RationalNormalCurve

universe u

/-- The standard grading of the full Hankel quotient by its homogeneous image
submodules. Its scalar action is the canonical quotient coefficient action.
For this fixed family the decomposition is unique; the instance makes the
graded-algebra operations available without choosing another decomposition. -/
noncomputable instance quotientHomogeneousGradedAlgebra (R : Type u) [CommRing R] (n : ℕ) :
    GradedAlgebra (quotientHomogeneousSubmodule R n) :=
  letI : SetLike.GradedMonoid (quotientHomogeneousSubmodule R n) := by
    refine { one_mem := ?_, mul_mem := ?_ }
    · exact Submodule.mem_map.mpr
        ⟨1, MvPolynomial.isHomogeneous_one (Fin (n + 1)) R,
          map_one (Ideal.Quotient.mkₐ R (hankelIdeal R n))⟩
    · intro i j x y hx hy
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
      exact Submodule.mem_map.mpr
        ⟨p * q, MvPolynomial.IsHomogeneous.mul hp hq,
          map_mul (Ideal.Quotient.mkₐ R (hankelIdeal R n)) p q⟩
  DirectSum.IsInternal.gradedAlgebra (quotientHomogeneousSubmodule_isInternal R n)

/-- The degree-zero ring homomorphism on the full Hankel quotient is coefficient
inclusion after coefficient augmentation. Both sides have codomain the full
quotient, over every commutative coefficient ring and for every parameter `n`. -/
theorem quotientHomogeneous_projZeroRingHom (R : Type u) [CommRing R] (n : ℕ) :
    GradedRing.projZeroRingHom (quotientHomogeneousSubmodule R n) =
      (algebraMap R (Source R n ⧸ hankelIdeal R n)).comp
        (quotientAugmentation R n).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change GradedRing.projZeroRingHom (quotientHomogeneousSubmodule R n)
        (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r)) =
      algebraMap R (Source R n ⧸ hankelIdeal R n)
        (quotientAugmentation R n
          (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r)))
    rw [quotientAugmentation_mk, MvPolynomial.constantCoeff_C]
    change (DirectSum.decompose (quotientHomogeneousSubmodule R n)
        (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r)) 0 :
          Source R n ⧸ hankelIdeal R n) =
      Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r)
    exact DirectSum.decompose_of_mem_same (quotientHomogeneousSubmodule R n)
      (Submodule.mem_map_of_mem (MvPolynomial.isHomogeneous_C (Fin (n + 1)) r))
  · intro i
    change GradedRing.projZeroRingHom (quotientHomogeneousSubmodule R n)
        (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) =
      algebraMap R (Source R n ⧸ hankelIdeal R n)
        (quotientAugmentation R n
          (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)))
    rw [quotientAugmentation_mk, MvPolynomial.constantCoeff_X, map_zero]
    exact DirectSum.decompose_of_mem_ne (quotientHomogeneousSubmodule R n)
      (Submodule.mem_map_of_mem (MvPolynomial.isHomogeneous_X R i)) (by decide)

end ToricIdeals.RationalNormalCurve
