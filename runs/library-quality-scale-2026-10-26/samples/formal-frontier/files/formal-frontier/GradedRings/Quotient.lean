/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients of graded rings

This file equips the quotient of a commutative graded ring by a homogeneous
ideal with the grading whose degree-`i` component is the image of the original
degree-`i` component.

Public data definitions retain their ordinary computational interface. The two
private construction helpers stay private: their necessary bodies are inlined
at exposed use sites, with private equalities to the original constructions.
-/

public section

open DirectSum

namespace Ideal.Quotient

universe u v w

variable {A : Type u} [CommRing A]
variable {ι : Type v} [DecidableEq ι] [AddMonoid ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

private def sourceComponent (i : ι) : AddSubgroup A where
  carrier := 𝒜 i
  zero_mem' := zero_mem (𝒜 i)
  add_mem' := add_mem
  neg_mem' := neg_mem

/-- The degree-`i` component of the quotient grading is the image of the
original degree-`i` component under the quotient map. -/
@[expose] def gradedComponent (i : ι) : AddSubgroup (A ⧸ I) :=
  AddSubgroup.map (Ideal.Quotient.mk I).toAddMonoidHom
    { carrier := 𝒜 i
      zero_mem' := zero_mem (𝒜 i)
      add_mem' := add_mem
      neg_mem' := neg_mem }

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
private theorem gradedComponent_eq_privateConstruction (i : ι) :
    gradedComponent 𝒜 I i =
      AddSubgroup.map (Ideal.Quotient.mk I).toAddMonoidHom (sourceComponent 𝒜 i) :=
  rfl

/-- The quotient map as a graded ring homomorphism for the image grading on the quotient. -/
@[expose] def gradedRingHom : 𝒜 →+*ᵍ gradedComponent 𝒜 I where
  toRingHom := Ideal.Quotient.mk I
  map_mem hx := ⟨_, hx, rfl⟩

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
@[simp]
theorem gradedRingHom_apply (x : A) : gradedRingHom 𝒜 I x = Ideal.Quotient.mk I x :=
  rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
@[simp]
theorem gradedRingHom_toRingHom : (gradedRingHom 𝒜 I).toRingHom = Ideal.Quotient.mk I :=
  rfl

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
/-- The graded quotient map is surjective on the underlying rings. -/
theorem gradedRingHom_surjective : Function.Surjective (gradedRingHom 𝒜 I) :=
  Ideal.Quotient.mk_surjective

/-- The image components of a quotient are closed under graded multiplication. -/
instance gradedComponentGradedMonoid :
    SetLike.GradedMonoid (gradedComponent 𝒜 I) where
  one_mem := by
    refine ⟨1, SetLike.one_mem_graded 𝒜, ?_⟩
    simp
  mul_mem i j x y hx hy := by
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    change a ∈ 𝒜 i at ha
    change b ∈ 𝒜 j at hb
    have hab : a * b ∈ 𝒜 (i + j) := SetLike.GradedMul.mul_mem ha hb
    refine ⟨a * b, hab, ?_⟩
    simp

/-- The additive map from an original graded component to its image in the quotient. -/
@[expose] def gradedComponentMap (i : ι) : 𝒜 i →+ gradedComponent 𝒜 I i where
  toFun x := ⟨Ideal.Quotient.mk I x, ⟨x, x.property, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Decompose an element of the original ring and map each component to the quotient. -/
@[expose] def gradedDecomposePre : A →+ ⨁ i, gradedComponent 𝒜 I i :=
  (DirectSum.map (gradedComponentMap 𝒜 I)).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

private theorem gradedDecomposePre_vanishes (hI : I.IsHomogeneous 𝒜) :
    (I : Submodule A A).toAddSubgroup ≤ (gradedDecomposePre 𝒜 I).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  apply DirectSum.ext
  intro i
  apply Subtype.ext
  change Ideal.Quotient.mk I (GradedRing.proj 𝒜 i x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (hI.mem_iff 𝒜).mp hx i

/-- Decompose a quotient class into the images of its homogeneous components. -/
@[expose] def gradedDecompose (hI : I.IsHomogeneous 𝒜) :
    (A ⧸ I) →+ ⨁ i, gradedComponent 𝒜 I i :=
  QuotientAddGroup.lift (I : Submodule A A).toAddSubgroup
    (gradedDecomposePre 𝒜 I) (by
      intro x hx
      rw [AddMonoidHom.mem_ker]
      apply DirectSum.ext
      intro i
      apply Subtype.ext
      change Ideal.Quotient.mk I (GradedRing.proj 𝒜 i x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (hI.mem_iff 𝒜).mp hx i)

private theorem gradedDecompose_eq_privateConstruction (hI : I.IsHomogeneous 𝒜) :
    gradedDecompose 𝒜 I hI =
      QuotientAddGroup.lift (I : Submodule A A).toAddSubgroup
        (gradedDecomposePre 𝒜 I) (gradedDecomposePre_vanishes 𝒜 I hI) :=
  rfl

@[simp]
theorem gradedDecompose_mk (hI : I.IsHomogeneous 𝒜) (x : A) :
    gradedDecompose 𝒜 I hI (Ideal.Quotient.mk I x) = gradedDecomposePre 𝒜 I x := by
  exact QuotientAddGroup.lift_mk _ _ x

@[simp]
theorem coe_gradedDecomposePre (x : A) :
    DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I) (gradedDecomposePre 𝒜 I x) =
      Ideal.Quotient.mk I x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous x =>
      simp [gradedDecomposePre, gradedComponentMap]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    exact (map_add (Ideal.Quotient.mk I) x y).symm

/-- Recombining the quotient decomposition gives the original quotient class. -/
theorem gradedDecompose_leftInverse (hI : I.IsHomogeneous 𝒜) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I))
      (gradedDecompose 𝒜 I hI) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [gradedDecompose_mk, coe_gradedDecomposePre]

/-- Decomposing a direct sum of quotient components gives the original sum. -/
theorem gradedDecompose_rightInverse (hI : I.IsHomogeneous 𝒜) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (gradedComponent 𝒜 I))
      (gradedDecompose 𝒜 I hI) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rcases y.property with ⟨a, ha, hya⟩
      have hy : y = gradedComponentMap 𝒜 I i ⟨a, ha⟩ := by
        apply Subtype.ext
        exact hya.symm
      rw [hy]
      rw [DirectSum.coeAddMonoidHom_of]
      change gradedDecompose 𝒜 I hI (Ideal.Quotient.mk I a) = _
      rw [gradedDecompose_mk]
      simp [gradedDecomposePre, gradedComponentMap,
        DirectSum.decompose_of_mem 𝒜 ha]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

/-- The natural direct-sum decomposition of a quotient by a homogeneous ideal. -/
@[expose, instance_reducible]
def gradedDecomposition (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (gradedComponent 𝒜 I) where
  decompose' := gradedDecompose 𝒜 I hI
  left_inv := gradedDecompose_leftInverse 𝒜 I hI
  right_inv := gradedDecompose_rightInverse 𝒜 I hI

/-- The natural grading on the quotient by a homogeneous ideal. -/
@[expose, instance_reducible]
def gradedRing (hI : I.IsHomogeneous 𝒜) :
    GradedRing (gradedComponent 𝒜 I) where
  toGradedMonoid := gradedComponentGradedMonoid 𝒜 I
  toDecomposition := gradedDecomposition 𝒜 I hI

end Ideal.Quotient
