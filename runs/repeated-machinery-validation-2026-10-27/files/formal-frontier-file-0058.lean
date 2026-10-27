/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularStageCoordinateRing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed superdiagonal stages of the unitriangular group scheme

The group objects below arise from quotient Hopf algebras, rather than
from a group law transported across an affine-space presentation.

Milne's finer filtration by individual entries gives closed algebraic subgroups
over a field, with these whole-superdiagonal stages at its block endpoints.
The Hopf quotients here include arbitrary commutative base rings and the empty
and singleton ranks.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 (unitriangular
  algebraic groups) and §6.49 (finer individual-entry stages and quotients).
* Mathlib contributors, `Mathlib.RingTheory.HopfAlgebra.Quotient`
  (quotient Hopf structure), `Mathlib.AlgebraicGeometry.Group.Affine`
  (`hopfSpec`), and `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
* The existing `Unitriangular` point equivalence is reused.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing
open scoped CategoryTheory MonObj TensorProduct

namespace AlgebraicGeometry

variable (K : Type) [CommRing K] (n r : ℕ)

open UnitriangularStageCoordinateRing

/-- The affine over-scheme represented by the stage quotient. -/
abbrev unitriangularStageUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (CoordinateRing K n r))).asOver (Spec (.of K))

/-- The group scheme represented by the stage quotient Hopf algebra.
Milne, *Algebraic Groups* (2017), §6.49 gives finer field-case
unitriangular algebraic subgroups; these stages remove whole superdiagonals. -/
abbrev unitriangularStageScheme : Grp (Over (Spec (.of K))) :=
  ⟨unitriangularStageUnderlyingScheme K n r⟩

/-- Closed inclusion into the existing unitriangular group scheme.
Milne, *Algebraic Groups* (2017), §6.49 gives finer closed field-case
subgroups whose superdiagonal block endpoints give these stages. -/
def unitriangularStageInclusion :
    unitriangularStageScheme K n r ⟶ unitriangularGroupScheme K (Fin n) :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (quotientBialgHom K n r)))

theorem unitriangularStageInclusion_left :
    (unitriangularStageInclusion K n r).hom.hom.left =
      Spec.map (CommRingCat.ofHom (quotient K n r).toRingHom) := rfl

theorem unitriangularStageInclusion_isClosedImmersion :
    IsClosedImmersion (unitriangularStageInclusion K n r).hom.hom.left := by
  rw [unitriangularStageInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Coordinate map for the successor stage, preserving the quotient Hopf structure. -/
def unitriangularStageSuccessorBialgHom :
    CoordinateRing K n r →ₐc[K] CoordinateRing K n (r + 1) := by
  apply BialgHom.ofAlgHom (successor K n r)
  · apply Ideal.Quotient.algHom_ext K
    change ((Bialgebra.counitAlgHom K (CoordinateRing K n (r + 1))).comp
      (successor K n r)).comp (quotient K n r) =
        (Bialgebra.counitAlgHom K (CoordinateRing K n r)).comp (quotient K n r)
    have hfactor : (successor K n r).comp (quotient K n r) =
        quotient K n (r + 1) := rfl
    rw [AlgHom.comp_assoc, hfactor]
    exact (BialgHom.counitAlgHom_comp (quotientBialgHom K n (r + 1))).trans
      (BialgHom.counitAlgHom_comp (quotientBialgHom K n r)).symm
  · apply Ideal.Quotient.algHom_ext K
    have hfactor : (successor K n r).comp (quotient K n r) =
        quotient K n (r + 1) := rfl
    have hcomul₀ := BialgHom.map_comp_comulAlgHom (quotientBialgHom K n r)
    have hcomul₁ := BialgHom.map_comp_comulAlgHom (quotientBialgHom K n (r + 1))
    change (Algebra.TensorProduct.map (quotient K n r) (quotient K n r)).comp
      (Bialgebra.comulAlgHom K (Ambient K n)) =
        (Bialgebra.comulAlgHom K (CoordinateRing K n r)).comp (quotient K n r) at hcomul₀
    change (Algebra.TensorProduct.map (quotient K n (r + 1)) (quotient K n (r + 1))).comp
      (Bialgebra.comulAlgHom K (Ambient K n)) =
        (Bialgebra.comulAlgHom K (CoordinateRing K n (r + 1))).comp
          (quotient K n (r + 1)) at hcomul₁
    change (((Algebra.TensorProduct.map (successor K n r) (successor K n r)).comp
      (Bialgebra.comulAlgHom K (CoordinateRing K n r))).comp (quotient K n r)) =
        (((Bialgebra.comulAlgHom K (CoordinateRing K n (r + 1))).comp
          (successor K n r)).comp (quotient K n r))
    rw [AlgHom.comp_assoc, ← hcomul₀, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp, hfactor, hcomul₁,
      AlgHom.comp_assoc, hfactor]

/-- Closed successor inclusion `S_(r+1) → S_r` induced by the Hopf quotient.
Milne, *Algebraic Groups* (2017), §6.49 orders individual-entry
field-case inclusions; the stage here removes an entire superdiagonal. -/
def unitriangularStageSuccessor :
    unitriangularStageScheme K n (r + 1) ⟶ unitriangularStageScheme K n r :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (unitriangularStageSuccessorBialgHom K n r)))

theorem unitriangularStageSuccessor_left :
    (unitriangularStageSuccessor K n r).hom.hom.left =
      Spec.map (CommRingCat.ofHom (successor K n r).toRingHom) := rfl

theorem unitriangularStageSuccessor_isClosedImmersion :
    IsClosedImmersion (unitriangularStageSuccessor K n r).hom.hom.left := by
  rw [unitriangularStageSuccessor_left]
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.factor_surjective (ideal_le_succ K n r)

set_option backward.isDefEq.respectTransparency false

/-- Successor and ambient closed embeddings commute as group-scheme maps. -/
theorem unitriangularStageSuccessor_inclusion :
    unitriangularStageSuccessor K n r ≫ unitriangularStageInclusion K n r =
      unitriangularStageInclusion K n (r + 1) := by
  unfold unitriangularStageSuccessor unitriangularStageInclusion
  rw [← Functor.map_comp]
  congr 1

variable (R : Type) [CommRing R] [Algebra K R]

/-- Descend evaluation of a filtered unitriangular matrix to the stage quotient. -/
def unitriangularStageFromGL
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    CoordinateRing K n r →ₐ[K] R :=
  Ideal.Quotient.liftₐ (ideal K n r)
    (unitriangularFromGL K (Fin n) R s.1) (by
      intro x hx
      have hs : unitriangularToGL K (Fin n) R
          (unitriangularFromGL K (Fin n) R s.1) ∈
          Matrix.UnitriangularGroup.superdiagonalSubgroup n R r := by
        simpa only [unitriangularToGL_fromGL] using s.2
      exact RingHom.mem_ker.mp
        ((mem_stage_iff K n r (unitriangularFromGL K (Fin n) R s.1)).mpr hs hx))

theorem unitriangularStageFromGL_comp_quotient
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    (unitriangularStageFromGL K n r R s).comp (quotient K n r) =
      unitriangularFromGL K (Fin n) R s.1 :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- Evaluating a quotient point gives a matrix in the existing stage subgroup. -/
def unitriangularStageToGL (f : CoordinateRing K n r →ₐ[K] R) :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r :=
  ⟨unitriangularToGL K (Fin n) R (f.comp (quotient K n r)),
    (mem_stage_iff K n r _).mp (by
      intro x hx
      apply RingHom.mem_ker.mpr
      change f ((quotient K n r) x) = 0
      have hzero : (quotient K n r) x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [hzero, map_zero])⟩

@[simp] theorem unitriangularStageToGL_fromGL
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    unitriangularStageToGL K n r R (unitriangularStageFromGL K n r R s) = s := by
  apply Subtype.ext
  change unitriangularToGL K (Fin n) R
    ((unitriangularStageFromGL K n r R s).comp (quotient K n r)) = s.1
  rw [unitriangularStageFromGL_comp_quotient]
  exact unitriangularToGL_fromGL K (Fin n) R s.1

@[simp] theorem unitriangularStageFromGL_toGL (f : CoordinateRing K n r →ₐ[K] R) :
    unitriangularStageFromGL K n r R (unitriangularStageToGL K n r R f) = f := by
  apply Ideal.Quotient.algHom_ext K
  change (unitriangularStageFromGL K n r R (unitriangularStageToGL K n r R f)).comp
      (quotient K n r) = f.comp (quotient K n r)
  rw [unitriangularStageFromGL_comp_quotient]
  change unitriangularFromGL K (Fin n) R
    (unitriangularToGL K (Fin n) R (f.comp (quotient K n r))) =
      f.comp (quotient K n r)
  exact unitriangularFromGL_toGL K (Fin n) R _

/-- The stage Hopf quotient represents the point subgroup multiplicatively.
Milne, *Algebraic Groups* (2017), item 2.9 represents the full unitriangular
field-case group; §6.49 gives finer subgroups with these block endpoints. -/
def unitriangularStageMulEquivAlgHom :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r ≃*
      WithConv (CoordinateRing K n r →ₐ[K] R) where
  toFun s := WithConv.toConv (unitriangularStageFromGL K n r R s)
  invFun φ := unitriangularStageToGL K n r R φ.ofConv
  left_inv s := unitriangularStageToGL_fromGL K n r R s
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact unitriangularStageFromGL_toGL K n r R φ.ofConv
  map_mul' s t := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext K
    change (unitriangularStageFromGL K n r R (s * t)).comp (quotient K n r) =
      ((WithConv.toConv (unitriangularStageFromGL K n r R s) *
        WithConv.toConv (unitriangularStageFromGL K n r R t)).ofConv).comp
          (quotientBialgHom K n r).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    rw [unitriangularStageFromGL_comp_quotient]
    change (unitriangularFromGL K (Fin n) R (s.1 * t.1)) =
      (WithConv.toConv ((unitriangularStageFromGL K n r R s).comp (quotient K n r)) *
        WithConv.toConv ((unitriangularStageFromGL K n r R t).comp (quotient K n r))).ofConv
    rw [unitriangularStageFromGL_comp_quotient,
      unitriangularStageFromGL_comp_quotient]
    exact congrArg WithConv.ofConv
      ((unitriangularGroupMulEquivAlgHom K (Fin n) R).map_mul s.1 t.1)

/-- Multiplicative identification with the points of the stage group scheme.
Milne, *Algebraic Groups* (2017), item 2.9 and §6.49 supply the
full-group and finer field-case subgroup antecedents. -/
def unitriangularStagePointMulEquiv :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ unitriangularStageUnderlyingScheme K n r) :=
  (unitriangularStageMulEquivAlgHom K n r R).trans
    (Spec.mapMulEquiv (R := K) (S := CoordinateRing K n r) (T := R))

theorem unitriangularStagePointMulEquiv_apply_left
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    (unitriangularStagePointMulEquiv K n r R s).left =
      Spec.map (CommRingCat.ofHom (unitriangularStageFromGL K n r R s).toRingHom) := rfl

/-- Coefficient change preserves each stage and its group law. -/
def unitriangularStageMap {S : Type} [CommRing S] (f : R →+* S) :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r →*
      Matrix.UnitriangularGroup.superdiagonalSubgroup n S r where
  toFun s := ⟨Matrix.UnitriangularGroup.map f s.1,
    Matrix.UnitriangularGroup.map_mem_superdiagonalSubgroup n R f s.2⟩
  map_one' := by
    apply Subtype.ext
    exact (Matrix.UnitriangularGroup.map f).map_one
  map_mul' s t := by
    apply Subtype.ext
    exact (Matrix.UnitriangularGroup.map f).map_mul s.1 t.1

theorem unitriangularStageFromGL_natural {S : Type} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    unitriangularStageFromGL K n r S (unitriangularStageMap n r R v.toRingHom s) =
      v.comp (unitriangularStageFromGL K n r R s) := by
  apply Ideal.Quotient.algHom_ext K
  change (unitriangularStageFromGL K n r S
      (unitriangularStageMap n r R v.toRingHom s)).comp (quotient K n r) =
        (v.comp (unitriangularStageFromGL K n r R s)).comp (quotient K n r)
  rw [AlgHom.comp_assoc, unitriangularStageFromGL_comp_quotient,
    unitriangularStageFromGL_comp_quotient]
  exact unitriangularFromGL_natural K (Fin n) R v s.1

/-- Underlying successor inclusion on the matrix groups. -/
def unitriangularStagePointSuccessor
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R (r + 1)) :
    Matrix.UnitriangularGroup.superdiagonalSubgroup n R r :=
  ⟨s.1, (Matrix.UnitriangularGroup.superdiagonalSubgroup_succ_le n R r) s.2⟩

/-- The successor quotient map represents the usual inclusion at every algebra. -/
theorem unitriangularStageFromGL_successor
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R (r + 1)) :
    (unitriangularStageFromGL K n (r + 1) R s).comp (successor K n r) =
      unitriangularStageFromGL K n r R (unitriangularStagePointSuccessor n r R s) := by
  apply Ideal.Quotient.algHom_ext K
  change ((unitriangularStageFromGL K n (r + 1) R s).comp
      (successor K n r)).comp (quotient K n r) =
        (unitriangularStageFromGL K n r R
          (unitriangularStagePointSuccessor n r R s)).comp (quotient K n r)
  have hfactor : (successor K n r).comp (quotient K n r) =
      quotient K n (r + 1) := rfl
  rw [AlgHom.comp_assoc, hfactor,
    unitriangularStageFromGL_comp_quotient,
    unitriangularStageFromGL_comp_quotient]
  rfl

/-- Successor agreement on scheme-valued points, for all coefficient algebras. -/
theorem unitriangularStageSuccessor_point
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R (r + 1)) :
    unitriangularStagePointMulEquiv K n (r + 1) R s ≫
        (unitriangularStageSuccessor K n r).hom.hom =
      unitriangularStagePointMulEquiv K n r R (unitriangularStagePointSuccessor n r R s) := by
  apply Over.OverMorphism.ext
  change ((unitriangularStagePointMulEquiv K n (r + 1) R s).left ≫
    (unitriangularStageSuccessor K n r).hom.hom.left) =
      (unitriangularStagePointMulEquiv K n r R
        (unitriangularStagePointSuccessor n r R s)).left
  rw [unitriangularStagePointMulEquiv_apply_left,
    unitriangularStagePointMulEquiv_apply_left, unitriangularStageSuccessor_left]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (AlgHom.congr_fun (unitriangularStageFromGL_successor K n r R s) x).symm

/-- The closed stage inclusion agrees with the underlying matrix embedding. -/
theorem unitriangularStageInclusion_point
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup n R r) :
    unitriangularStagePointMulEquiv K n r R s ≫
        (unitriangularStageInclusion K n r).hom.hom =
      unitriangularGroupMulEquivPoints K (Fin n) R s.1 := by
  apply Over.OverMorphism.ext
  change ((unitriangularStagePointMulEquiv K n r R s).left ≫
    (unitriangularStageInclusion K n r).hom.hom.left) =
      (unitriangularGroupMulEquivPoints K (Fin n) R s.1).left
  rw [unitriangularStagePointMulEquiv_apply_left,
    unitriangularStageInclusion_left, unitriangularGroupMulEquivPoints_apply_left,
    ← Spec.map_comp]
  congr 1

/-- The filtration of matrix groups as a functor on all `K`-algebras. -/
def unitriangularStageFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.UnitriangularGroup.superdiagonalSubgroup n R r)
  map f := GrpCat.ofHom (unitriangularStageMap n r _ f.hom.toRingHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

/-- Represented group-valued point functor of a Hopf quotient. -/
abbrev unitriangularStagePointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (unitriangularStageScheme K n r)

/-- Natural multiplicative identification of stage points for every `K`-algebra.
Milne, *Algebraic Groups* (2017), item 2.9 describes the unitriangular
group functor and §6.49 its finer field-case stages; this is the
whole-superdiagonal subgroup functor over arbitrary commutative bases. -/
def unitriangularStagePointsIso :
    unitriangularStageFunctor K n r ≅ unitriangularStagePointsFunctor K n r :=
  NatIso.ofComponents
    (fun R => (unitriangularStagePointMulEquiv K n r R).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change (unitriangularStagePointMulEquiv K n r S
        (unitriangularStageMap n r R f.hom.toRingHom s)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (unitriangularStagePointMulEquiv K n r R s).left
      rw [unitriangularStagePointMulEquiv_apply_left,
        unitriangularStagePointMulEquiv_apply_left]
      have hbase : ((algSpec (.of K)).map f.op).left =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) := rfl
      rw [hbase, ← Spec.map_comp]
      congr 1
      ext x
      exact AlgHom.congr_fun (unitriangularStageFromGL_natural K n r R f.hom s) x)

end AlgebraicGeometry
