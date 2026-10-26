/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStages
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Normality of the closed unitriangular stages

The closed immersion of each superdiagonal stage is a normal morphism of group
objects over an arbitrary commutative ring. Conjugation is factored as a map of
over-schemes, not as a group homomorphism from the product. Its affine product
is the spectrum of the tensor product of the two coordinate algebras; the
universal point conjugates into the stage by normality of the matrix subgroup.
The stage-point equivalence descends this point through the quotient algebra.

Milne's finer field-case filtration consists of subgroups normal even in the
upper-triangular group; its superdiagonal block endpoints give field-case
whole stages. This module proves normality in the unitriangular group scheme
over arbitrary commutative rings.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 6.36 and §6.49
  (nilpotence and normality of the finer field-case filtration).
* Mathlib contributors, `Mathlib.CategoryTheory.Monoidal.Cartesian.Normal`
  (`IsMonHom.Normal`) and `Mathlib.AlgebraicGeometry.Pullbacks`
  (`pullbackSpecIso`).
* The existing `UnitriangularCentralFiltration` supplies subgroup normality
  for every coefficient ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped CategoryTheory MonObj TensorProduct MonoidalCategory

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

namespace UnitriangularStageNormality

abbrev ambientRing := UnitriangularCoordinateRing.CoordinateRing K (Fin n)
abbrev stageRing := UnitriangularStageCoordinateRing.CoordinateRing K n r

/-- The algebra of functions on the affine product of the ambient group and a stage. -/
abbrev productRing :=
  @TensorProduct K (CommRing.toCommSemiring : CommSemiring K)
    (ambientRing K n) (stageRing K n r)
    ((CommRing.toCommSemiring : CommSemiring (ambientRing K n)).toAddCommMonoid)
    ((CommRing.toCommSemiring : CommSemiring (stageRing K n r)).toAddCommMonoid)
    (Algebra.toModule (R := K) (A := ambientRing K n))
    (Algebra.toModule (R := K) (A := stageRing K n r))

/-- The relative product of the two affine schemes is represented by their
tensor-product coordinate ring. -/
def stageProductIso :
    (unitriangularGroupScheme K (Fin n)).X ⊗ (unitriangularStageScheme K n r).X ≅
      (Spec (.of (productRing K n r))).asOver (Spec (.of K)) := by
  refine Over.isoMk (pullbackSpecIso K (ambientRing K n) (stageRing K n r)) ?_
  rw [Over.tensorObj_hom]
  exact pullbackSpecIso_hom_base K (ambientRing K n) (stageRing K n r)

instance stageInclusion_mono : Mono (unitriangularStageInclusion K n r).hom.hom := by
  have : IsClosedImmersion (unitriangularStageInclusion K n r).hom.hom.left :=
    unitriangularStageInclusion_isClosedImmersion K n r
  exact Over.mono_of_mono_left _

/-- Normality of the matrix subgroup sends the universal conjugate into the stage. -/
def affineConjugate (R : Type) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ (unitriangularGroupScheme K (Fin n)).X)
    (s : (Spec (.of R)).asOver (Spec (.of K)) ⟶ (unitriangularStageScheme K n r).X) :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r := by
  let u := (unitriangularGroupMulEquivPoints K (Fin n) R).symm g
  let v := (unitriangularStagePointMulEquiv K n r R).symm s
  exact ⟨u * v.1 * u⁻¹,
    (inferInstance : (Matrix.UnitriangularGroup.superdiagonalSubgroup n R r).Normal).conj_mem
      v.1 v.2 u⟩

/-- The stage quotient evaluates to the matrix conjugate on every affine point. -/
theorem affineConjugate_inclusion (R : Type) [CommRing R] [Algebra K R]
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ (unitriangularGroupScheme K (Fin n)).X)
    (s : (Spec (.of R)).asOver (Spec (.of K)) ⟶ (unitriangularStageScheme K n r).X) :
    unitriangularStagePointMulEquiv K n r R (affineConjugate K n r R g s) ≫
      (unitriangularStageInclusion K n r).hom.hom =
        g * (s ≫ (unitriangularStageInclusion K n r).hom.hom) * g⁻¹ := by
  let u := (unitriangularGroupMulEquivPoints K (Fin n) R).symm g
  let v := (unitriangularStagePointMulEquiv K n r R).symm s
  rw [unitriangularStageInclusion_point]
  change unitriangularGroupMulEquivPoints K (Fin n) R (u * v.1 * u⁻¹) = _
  simp only [map_mul, map_inv]
  have hu : unitriangularGroupMulEquivPoints K (Fin n) R u = g :=
    (unitriangularGroupMulEquivPoints K (Fin n) R).apply_symm_apply g
  have hv : unitriangularGroupMulEquivPoints K (Fin n) R v.1 =
      s ≫ (unitriangularStageInclusion K n r).hom.hom := by
    rw [← unitriangularStageInclusion_point K n r R v]
    exact congrArg (fun t => t ≫ (unitriangularStageInclusion K n r).hom.hom)
      ((unitriangularStagePointMulEquiv K n r R).apply_symm_apply s)
  rw [hu, hv]

end UnitriangularStageNormality

open UnitriangularStageNormality

/-- Conjugation by the ambient group, factored through the closed stage in
`Over (Spec K)`. The factor is not asserted to preserve the product group law.
Milne, *Algebraic Groups* (2017), §6.49(a) proves normality for the finer
field-case filtration, including these superdiagonal block endpoints. -/
def unitriangularStageConjugation :
    (unitriangularGroupScheme K (Fin n)).X ⊗
      (unitriangularStageScheme K n r).X ⟶ (unitriangularStageScheme K n r).X :=
  let e := stageProductIso K n r
  e.hom ≫ unitriangularStagePointMulEquiv K n r (productRing K n r)
    (affineConjugate K n r (productRing K n r)
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.fst _ _)
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.snd _ _))

/-- The factored map is the genuine categorical ambient conjugation after
composing with the closed immersion. -/
theorem unitriangularStageConjugation_inclusion :
    unitriangularStageConjugation K n r ≫ (unitriangularStageInclusion K n r).hom.hom =
        (unitriangularGroupScheme K (Fin n)).X ◁
          (unitriangularStageInclusion K n r).hom.hom ≫
          CategoryTheory.GrpObj.conj (unitriangularGroupScheme K (Fin n)).X := by
  let e := stageProductIso K n r
  let f := (unitriangularStageInclusion K n r).hom.hom
  have ht := affineConjugate_inclusion K n r (productRing K n r)
    (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.fst _ _)
    (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.snd _ _)
  change (e.hom ≫ unitriangularStagePointMulEquiv K n r (productRing K n r)
    (affineConjugate K n r (productRing K n r)
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.fst _ _)
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.snd _ _))) ≫ f = _
  apply (cancel_epi e.inv).mp
  have hc : e.inv ≫ ((unitriangularGroupScheme K (Fin n)).X ◁ f ≫
      CategoryTheory.GrpObj.conj (unitriangularGroupScheme K (Fin n)).X) =
      (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.fst _ _) *
        ((e.inv ≫ CategoryTheory.CartesianMonoidalCategory.snd _ _) ≫ f) *
        (e.inv ≫ CategoryTheory.CartesianMonoidalCategory.fst _ _)⁻¹ := by
    simp [CategoryTheory.GrpObj.conj, MonObj.comp_mul, CategoryTheory.GrpObj.comp_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at *
  exact ht.trans hc.symm

/-- Each closed superdiagonal stage is a normal subgroup object, including
ranks zero and one and zero base rings. Milne, *Algebraic Groups* (2017),
§6.49 gives a finer field-case normal filtration whose superdiagonal block
endpoints antecede these whole stages. -/
instance unitriangularStageInclusion_normal :
    CategoryTheory.IsMonHom.Normal (unitriangularStageInclusion K n r).hom.hom where
  exists_comp_eq_conj := ⟨unitriangularStageConjugation K n r,
    unitriangularStageConjugation_inclusion K n r⟩

/-- At every `K`-algebra, the categorical factor is the usual matrix
conjugation. Its naturality follows from composition with algebra maps. -/
theorem unitriangularStageConjugation_point (R : Type) [CommRing R] [Algebra K R]
    (g : Matrix.UnitriangularGroup (Fin n) R)
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    CategoryTheory.CartesianMonoidalCategory.lift
        (unitriangularGroupMulEquivPoints K (Fin n) R g)
        (unitriangularStagePointMulEquiv K n r R s) ≫
      unitriangularStageConjugation K n r =
        unitriangularStagePointMulEquiv K n r R
          ⟨g * s.1 * g⁻¹,
            (inferInstance : (Matrix.UnitriangularGroup.superdiagonalSubgroup n R r).Normal).conj_mem
              s.1 s.2 g⟩ := by
  let f := (unitriangularStageInclusion K n r).hom.hom
  apply (cancel_mono f).mp
  rw [Category.assoc, unitriangularStageConjugation_inclusion]
  have hs := unitriangularStageInclusion_point K n r R s
  have ht := unitriangularStageInclusion_point K n r R
    (⟨g * s.1 * g⁻¹,
      (inferInstance : (Matrix.UnitriangularGroup.superdiagonalSubgroup n R r).Normal).conj_mem
        s.1 s.2 g⟩ : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r)
  rw [ht]
  change _ = unitriangularGroupMulEquivPoints K (Fin n) R (g * s.1 * g⁻¹)
  rw [map_mul, map_mul, map_inv]
  rw [← hs]
  simp [CategoryTheory.GrpObj.conj, MonObj.comp_mul, CategoryTheory.GrpObj.comp_inv]

end AlgebraicGeometry
