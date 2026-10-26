/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
public import AlgebraicGroups.GroupScheme.RootsOfUnity

public section

/-!
# The first-power infinitesimal additive group scheme

The quotient by the first power of the additive coordinate is the base Hopf
algebra. Its native group scheme is therefore isomorphic to the group scheme
represented by the group algebra on the one-element additive group.

This is the `m = 0` boundary of the characteristic-power example in Milne's
*Algebraic Groups*, item 2.5: both group schemes are trivial here, so the
unqualified non-isomorphism assertion there does not hold at this exponent.
The isomorphism is a group-object isomorphism over any commutative base of
prime characteristic, not only an underlying-scheme isomorphism over a field.

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.5, p. 40 (the
  characteristic-power and roots-of-unity constructions and their boundary case).
- Mathlib, `Mathlib.RingTheory.Bialgebra.Hom`,
  `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`, and
  `Mathlib.AlgebraicGeometry.Group.Affine` (the bialgebra counit,
  singleton group-algebra equivalence and affine Hopf `Spec` construction).
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The native counit identifies the first-power additive quotient with the
base bialgebra; its inverse is the native algebra map. -/
@[expose] def infinitesimalAdditiveZeroBialgEquiv :
    infinitesimalAdditiveCoordinateRing K p 0 ≃ₐc[K] K where
  __ := Bialgebra.counitBialgHom K _
  invFun := algebraMap K _
  left_inv x := by
    let A := infinitesimalAdditiveCoordinateRing K p 0
    have hsub (a b : Multiplicative (infinitesimalAdditiveSubgroup K p 0 A)) : a = b := by
      exact congrArg Multiplicative.ofAdd
        ((infinitesimalAdditiveSubgroup_zero_eq_zero K p A a.toAdd).trans
          (infinitesimalAdditiveSubgroup_zero_eq_zero K p A b.toAdd).symm)
    have hmaps : (Algebra.ofId K A).comp (Bialgebra.counitAlgHom K A) =
        AlgHom.id K A := by
      apply WithConv.toConv_injective
      apply (infinitesimalAdditiveMulEquivAlgHom K p 0 A).symm.injective
      exact hsub _ _
    exact congrArg (fun f : A →ₐ[K] A => f x) hmaps
  right_inv r := Bialgebra.counit_algebraMap r

/-- The equivalence evaluates to the native counit. -/
@[simp]
theorem infinitesimalAdditiveZeroBialgEquiv_apply
    (x : infinitesimalAdditiveCoordinateRing K p 0) :
    infinitesimalAdditiveZeroBialgEquiv K p x = CoalgebraStruct.counit (R := K) x := rfl

/-- The inverse equivalence is the native algebra map. -/
@[simp]
theorem infinitesimalAdditiveZeroBialgEquiv_symm_apply (r : K) :
    (infinitesimalAdditiveZeroBialgEquiv K p).symm r =
      algebraMap K (infinitesimalAdditiveCoordinateRing K p 0) r := rfl

/-- The distinguished first-power coordinate evaluates to zero. -/
theorem infinitesimalAdditiveZeroBialgEquiv_coordinate :
    infinitesimalAdditiveZeroBialgEquiv K p (infinitesimalAdditiveCoordinate K p 0) =
      0 := by
  simp

/-- The first-power infinitesimal additive group scheme is isomorphic to the
order-one roots-of-unity group scheme as a group object over `Spec K`. This
`m = 0` case corrects the unrestricted non-isomorphism assertion in Milne's
*Algebraic Groups*, item 2.5. -/
@[expose] def infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne :
    infinitesimalAdditiveGroupScheme K p 0 ≅ rootsOfUnityGroupScheme K 1 :=
  (hopfSpec (.of K)).mapIso
    (CommHopfAlgCat.isoMk ((infinitesimalAdditiveZeroBialgEquiv K p).trans
      (AddMonoidAlgebra.bialgEquivOfSubsingleton (R := K) (M := ZMod 1)).symm)).symm.op

/-- The forward scheme map is induced contravariantly by the inverse of the
coordinate bialgebra equivalence. -/
theorem infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne_hom_left :
    (infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne K p).hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (((infinitesimalAdditiveZeroBialgEquiv K p).symm :
            K →ₐ[K] infinitesimalAdditiveCoordinateRing K p 0).comp
          (AddMonoidAlgebra.bialgEquivOfSubsingleton (R := K) (M := ZMod 1) :
            rootsOfUnityCoordinateRing K 1 →ₐ[K] K)).toRingHom) := rfl

/-- The inverse scheme map uses the native counit followed by the inverse of
the order-one group algebra's counit. -/
theorem infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne_inv_left :
    (infinitesimalAdditiveGroupSchemeZeroIsoRootsOfUnityOne K p).inv.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (((AddMonoidAlgebra.bialgEquivOfSubsingleton (R := K) (M := ZMod 1)).symm :
            K →ₐ[K] rootsOfUnityCoordinateRing K 1).comp
          (infinitesimalAdditiveZeroBialgEquiv K p :
            infinitesimalAdditiveCoordinateRing K p 0 →ₐ[K] K)).toRingHom) := rfl

end AlgebraicGeometry
