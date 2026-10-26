/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.PrimitivePowerHopfIdeal
public import AlgebraicGroups.GroupScheme.Additive
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Characteristic-power infinitesimal additive group schemes

Over a commutative ring of prime characteristic `p`, the quotient of the additive
coordinate Hopf algebra by the `p ^ m`-th power of its primitive coordinate
represents the additive group of elements whose `p ^ m`-th power vanishes.
The construction includes `m = 0` and works with arbitrary test algebras,
including the zero algebra.

This represents the characteristic-power additive group in Milne's
*Algebraic Groups*, item 2.5, where the base is a field. The Hopf quotient
here instead uses the general primitive-power Hopf-ideal theorem, and the
nilpotent-element functor and its affine points are defined over every
commutative base of prime characteristic. A test algebra need not have
characteristic *exactly* `p` or an injective structure map.

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.5, p. 40 (nilpotent
  points, the additive law, quotient coordinates and comultiplication).
- `AlgebraicGroups.Algebra.PrimitivePowerHopfIdeal` and
  `AlgebraicGroups.GroupScheme.Additive` (the general quotient-Hopf criterion
  and the additive coordinate and point equivalences used here).
- Mathlib, `Mathlib.Algebra.CharP.Lemmas`,
  `Mathlib.RingTheory.HopfAlgebra.Quotient`, and
  `Mathlib.AlgebraicGeometry.Group.Affine` (prime-power binomial identities,
  quotient Hopf structure and affine point/convolution transport).
-/

public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

/-- The characteristic-power ideal in the additive coordinate Hopf algebra. -/
abbrev infinitesimalAdditiveIdeal : Ideal (additiveGroupCoordinateRing K) :=
  Ideal.span {(additiveGroupCoordinate K) ^ (p ^ m)}

private theorem infinitesimalAdditive_primitive :
    Bialgebra.IsPrimitiveElem K (additiveGroupCoordinate K) := by
  constructor
  · simp
  · simpa only [add_comm] using additiveGroupCoordinate_comul K

instance infinitesimalAdditiveIdeal_isHopfIdeal :
    Ideal.IsHopfIdeal K (infinitesimalAdditiveIdeal K p m) :=
  (infinitesimalAdditive_primitive K).isHopfIdeal_span_pow_char_pow m

/-- The coordinate Hopf algebra of the characteristic-power infinitesimal
additive group in Milne's *Algebraic Groups*, item 2.5, extended from fields
to commutative bases of prime characteristic. -/
abbrev infinitesimalAdditiveCoordinateRing :=
  additiveGroupCoordinateRing K ⧸ infinitesimalAdditiveIdeal K p m

/-- The image of the additive coordinate in the quotient Hopf algebra. -/
@[expose] def infinitesimalAdditiveCoordinate : infinitesimalAdditiveCoordinateRing K p m :=
  (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)) (additiveGroupCoordinate K)

omit [Fact p.Prime] [CharP K p] in
@[simp]
theorem infinitesimalAdditiveCoordinate_pow :
    infinitesimalAdditiveCoordinate K p m ^ (p ^ m) = 0 := by
  change (Ideal.Quotient.mk (infinitesimalAdditiveIdeal K p m)
    (additiveGroupCoordinate K)) ^ (p ^ m) = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

@[simp]
theorem infinitesimalAdditiveCoordinate_comul :
    CoalgebraStruct.comul (infinitesimalAdditiveCoordinate K p m) =
      infinitesimalAdditiveCoordinate K p m ⊗ₜ[K] 1 +
        1 ⊗ₜ[K] infinitesimalAdditiveCoordinate K p m := by
  rw [show infinitesimalAdditiveCoordinate K p m =
      Ideal.Quotient.mk (infinitesimalAdditiveIdeal K p m) (additiveGroupCoordinate K) from rfl,
    Bialgebra.Quotient.comul_mk, additiveGroupCoordinate_comul]
  simp

@[simp]
theorem infinitesimalAdditiveCoordinate_counit :
    CoalgebraStruct.counit (R := K) (infinitesimalAdditiveCoordinate K p m) = 0 := by
  exact additiveGroupCoordinate_counit K

@[simp]
theorem infinitesimalAdditiveCoordinate_antipode :
    (HopfAlgebraStruct.antipode K) (infinitesimalAdditiveCoordinate K p m) =
      -infinitesimalAdditiveCoordinate K p m := by
  rw [show infinitesimalAdditiveCoordinate K p m =
      Ideal.Quotient.mk (infinitesimalAdditiveIdeal K p m) (additiveGroupCoordinate K) from rfl,
    HopfAlgebra.Quotient.antipode_mk, additiveGroupCoordinate_antipode]
  rfl

instance infinitesimalAdditiveCoordinateRing_finiteType :
    Algebra.FiniteType K (infinitesimalAdditiveCoordinateRing K p m) := by
  exact Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m))
    Ideal.Quotient.mk_surjective

/-- The affine scheme represented by the characteristic-power quotient. -/
abbrev infinitesimalAdditiveUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (infinitesimalAdditiveCoordinateRing K p m))).asOver (Spec (.of K))

instance infinitesimalAdditiveUnderlyingScheme_locallyOfFiniteType :
    LocallyOfFiniteType (infinitesimalAdditiveUnderlyingScheme K p m).hom := by
  let _ : Algebra.FiniteType K (infinitesimalAdditiveCoordinateRing K p m) :=
    infinitesimalAdditiveCoordinateRing_finiteType K p m
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (infinitesimalAdditiveCoordinateRing K p m))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

instance infinitesimalAdditiveUnderlyingScheme_quasiCompact :
    QuasiCompact (infinitesimalAdditiveUnderlyingScheme K p m).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (infinitesimalAdditiveCoordinateRing K p m))))
  infer_instance

/-- The group scheme attached to the quotient Hopf algebra, representing
Milne's *Algebraic Groups*, item 2.5, over fields and more generally over
commutative bases of prime characteristic. -/
abbrev infinitesimalAdditiveGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨infinitesimalAdditiveUnderlyingScheme K p m⟩

variable (R : Type u) [CommRing R] [Algebra K R]

include K

omit [Fact p.Prime] in
private theorem infinitesimalAdditive_char_target : (p : R) = 0 := by
  calc
    (p : R) = algebraMap K R (p : K) := (map_natCast (algebraMap K R) p).symm
    _ = 0 := by rw [CharP.cast_eq_zero K p]; simp

/-- The additive subgroup of `p ^ m`-nilpotent elements of a test algebra. -/
@[expose] def infinitesimalAdditiveSubgroup : AddSubgroup R where
  carrier := {r : R | r ^ (p ^ m) = 0}
  zero_mem' := by
    change (0 : R) ^ (p ^ m) = 0
    exact zero_pow (pow_pos (Fact.out : p.Prime).pos m).ne'
  add_mem' := by
    intro r s hr hs
    change (r + s) ^ (p ^ m) = 0
    rw [(Commute.all r s).add_pow_prime_pow_eq' (Fact.out : p.Prime) m,
      infinitesimalAdditive_char_target K p R, zero_mul, add_zero]
    exact (by change r ^ (p ^ m) = 0 at hr; change s ^ (p ^ m) = 0 at hs
              simp [hr, hs])
  neg_mem' := by
    intro r hr
    change (-r) ^ (p ^ m) = 0
    change r ^ (p ^ m) = 0 at hr
    rw [neg_pow, hr, mul_zero]

@[simp]
theorem mem_infinitesimalAdditiveSubgroup (r : R) :
    r ∈ infinitesimalAdditiveSubgroup K p m R ↔ r ^ (p ^ m) = 0 := Iff.rfl

/-- At exponent one, the nilpotent subgroup consists only of zero. -/
theorem infinitesimalAdditiveSubgroup_zero_eq_bot :
    infinitesimalAdditiveSubgroup K p 0 R = ⊥ := by
  ext r
  simp [mem_infinitesimalAdditiveSubgroup]

/-- Every point of the first-power quotient has coordinate zero. -/
theorem infinitesimalAdditiveSubgroup_zero_eq_zero
    (r : infinitesimalAdditiveSubgroup K p 0 R) : r = 0 := by
  apply Subtype.ext
  change r.val = (0 : R)
  have hr : r.val ^ (p ^ 0) = 0 := r.property
  simpa only [pow_zero, pow_one] using hr

/-- Postcomposition takes `p ^ m`-nilpotent points to `p ^ m`-nilpotent points. -/
@[expose] def infinitesimalAdditiveMap {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) :
    infinitesimalAdditiveSubgroup K p m R →+
      infinitesimalAdditiveSubgroup K p m S where
  toFun r := ⟨f r.val, by rw [mem_infinitesimalAdditiveSubgroup, ← map_pow, r.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' r s := Subtype.ext (map_add f r.val s.val)

/-- The group-valued functor of characteristic-power nilpotent elements from
Milne's *Algebraic Groups*, item 2.5, defined on every commutative test
algebra over a base of prime characteristic. -/
@[expose] def infinitesimalAdditiveFunctor : CommAlgCat K ⥤ GrpCat where
  obj S := GrpCat.of (Multiplicative (infinitesimalAdditiveSubgroup K p m S))
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    (infinitesimalAdditiveMap K p m _ f.hom))
  map_id _ := by
    apply GrpCat.hom_ext
    rfl
  map_comp _ _ := by
    apply GrpCat.hom_ext
    rfl

/-- The affine group scheme's group-valued functor of points. -/
abbrev infinitesimalAdditivePointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (infinitesimalAdditiveGroupScheme K p m)

private def infinitesimalAdditiveLift
    (r : infinitesimalAdditiveSubgroup K p m R) :
    infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R :=
  Ideal.Quotient.liftₐ (infinitesimalAdditiveIdeal K p m)
    (additiveGroupMulEquivAlgHom K R (.ofAdd r.val)).ofConv (by
      intro x hx
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx
      rw [← hb, map_mul, map_pow, additiveGroupMulEquivAlgHom_coordinate,
        r.property, mul_zero])

private theorem infinitesimalAdditiveLift_coordinate
    (r : infinitesimalAdditiveSubgroup K p m R) :
    infinitesimalAdditiveLift K p m R r (infinitesimalAdditiveCoordinate K p m) = r.val := by
  exact additiveGroupMulEquivAlgHom_coordinate K R r.val

private theorem infinitesimalAdditiveLift_comp_mk
    (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveLift K p m R r).comp
      (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)) =
        (additiveGroupMulEquivAlgHom K R (.ofAdd r.val)).ofConv := by
  exact Ideal.Quotient.liftₐ_comp _ _ _

/-- Evaluation at the quotient coordinate identifies convolution homomorphisms
with characteristic-power nilpotent elements, including for zero test algebras. -/
@[expose] def infinitesimalAdditiveMulEquivAlgHom :
    Multiplicative (infinitesimalAdditiveSubgroup K p m R) ≃*
      WithConv (infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R) where
  toFun r := WithConv.toConv (Ideal.Quotient.liftₐ (infinitesimalAdditiveIdeal K p m)
    (additiveGroupMulEquivAlgHom K R (.ofAdd r.toAdd.val)).ofConv (by
      intro x hx
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx
      rw [← hb, map_mul, map_pow, additiveGroupMulEquivAlgHom_coordinate,
        r.toAdd.property, mul_zero]))
  invFun f := Multiplicative.ofAdd ⟨f.ofConv (infinitesimalAdditiveCoordinate K p m), by
    change (f.ofConv (infinitesimalAdditiveCoordinate K p m)) ^ (p ^ m) = 0
    rw [← map_pow, infinitesimalAdditiveCoordinate_pow, map_zero]⟩
  left_inv r := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd r.toAdd
    congr 1
    apply Subtype.ext
    exact infinitesimalAdditiveLift_coordinate K p m R r.toAdd
  right_inv f := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext
    change (infinitesimalAdditiveLift K p m R
      ⟨f.ofConv (infinitesimalAdditiveCoordinate K p m), by
        change (f.ofConv (infinitesimalAdditiveCoordinate K p m)) ^ (p ^ m) = 0
        rw [← map_pow, infinitesimalAdditiveCoordinate_pow, map_zero]⟩).comp
      (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)) =
        f.ofConv.comp (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m))
    rw [infinitesimalAdditiveLift_comp_mk]
    apply SymmetricAlgebra.algHom_ext
    ext
    exact additiveGroupMulEquivAlgHom_coordinate K R
      (f.ofConv (infinitesimalAdditiveCoordinate K p m))
  map_mul' r s := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext
    change (infinitesimalAdditiveLift K p m R (r * s).toAdd).comp
      (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)) =
      ((WithConv.toConv (infinitesimalAdditiveLift K p m R r.toAdd)) *
        (WithConv.toConv (infinitesimalAdditiveLift K p m R s.toAdd))).ofConv.comp
          (Bialgebra.Quotient.mkBialgHom (infinitesimalAdditiveIdeal K p m)).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib
      (WithConv.toConv (infinitesimalAdditiveLift K p m R r.toAdd))
      (WithConv.toConv (infinitesimalAdditiveLift K p m R s.toAdd))
      (Bialgebra.Quotient.mkBialgHom (infinitesimalAdditiveIdeal K p m))]
    rw [infinitesimalAdditiveLift_comp_mk]
    change ((additiveGroupMulEquivAlgHom K R) (.ofAdd (r.toAdd.val + s.toAdd.val))).ofConv =
      (WithConv.toConv ((infinitesimalAdditiveLift K p m R r.toAdd).comp
        (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m))) *
       WithConv.toConv ((infinitesimalAdditiveLift K p m R s.toAdd).comp
         (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)))).ofConv
    rw [infinitesimalAdditiveLift_comp_mk, infinitesimalAdditiveLift_comp_mk]
    exact congrArg WithConv.ofConv
      ((additiveGroupMulEquivAlgHom K R).map_mul (.ofAdd r.toAdd.val) (.ofAdd s.toAdd.val))

@[simp]
theorem infinitesimalAdditiveMulEquivAlgHom_coordinate
    (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv
      (infinitesimalAdditiveCoordinate K p m) = r.val :=
  infinitesimalAdditiveLift_coordinate K p m R r

@[simp]
theorem infinitesimalAdditiveMulEquivAlgHom_symm_coordinate
    (f : WithConv (infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R)) :
    ((infinitesimalAdditiveMulEquivAlgHom K p m R).symm f).toAdd.val =
      f.ofConv (infinitesimalAdditiveCoordinate K p m) := rfl

/-- Convolution of nilpotent-point homomorphisms evaluates to literal addition. -/
theorem infinitesimalAdditiveMulEquivAlgHom_add
    (r s : infinitesimalAdditiveSubgroup K p m R) :
    infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd (r + s)) =
      infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r) *
        infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd s) :=
  (infinitesimalAdditiveMulEquivAlgHom K p m R).map_mul _ _

/-- The distinguished coordinate of the convolution product evaluates to the
ordinary sum in the test algebra. -/
theorem infinitesimalAdditiveConvolution_coordinate
    (r s : infinitesimalAdditiveSubgroup K p m R) :
    ((infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r) *
      infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd s)).ofConv
        (infinitesimalAdditiveCoordinate K p m)) = r.val + s.val := by
  rw [← infinitesimalAdditiveMulEquivAlgHom_add,
    infinitesimalAdditiveMulEquivAlgHom_coordinate]
  rfl

/-- Evaluation and the quotient universal property commute with algebra maps. -/
theorem infinitesimalAdditiveMulEquivAlgHom_naturality
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveMulEquivAlgHom K p m S
      (.ofAdd (infinitesimalAdditiveMap K p m R f r))).ofConv =
        f.comp (infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv := by
  apply Ideal.Quotient.algHom_ext
  change (infinitesimalAdditiveLift K p m S (infinitesimalAdditiveMap K p m R f r)).comp
      (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)) =
    (f.comp (infinitesimalAdditiveLift K p m R r)).comp
      (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m))
  rw [AlgHom.comp_assoc, infinitesimalAdditiveLift_comp_mk,
    infinitesimalAdditiveLift_comp_mk]
  exact additiveGroupMulEquivAlgHom_naturality K R f r.val

/-- Affine points of the quotient group scheme are exactly nilpotent elements,
with their additive group law. -/
@[expose] def infinitesimalAdditiveMulEquivPoints :
    Multiplicative (infinitesimalAdditiveSubgroup K p m R) ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (infinitesimalAdditiveGroupScheme K p m).X) :=
  (infinitesimalAdditiveMulEquivAlgHom K p m R).trans
    (Spec.mapMulEquiv (R := K) (S := infinitesimalAdditiveCoordinateRing K p m) (T := R))

@[simp]
theorem infinitesimalAdditiveMulEquivPoints_apply_left
    (r : infinitesimalAdditiveSubgroup K p m R) :
    (infinitesimalAdditiveMulEquivPoints K p m R (.ofAdd r)).left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv.toRingHom) := rfl

/-- Read the quotient coordinate from the algebra map underlying a scheme point. -/
@[simp]
theorem infinitesimalAdditiveMulEquivPoints_symm_coordinate
    (f : (Spec (.of R)).asOver (Spec (.of K)) ⟶
      (infinitesimalAdditiveGroupScheme K p m).X) :
    ((infinitesimalAdditiveMulEquivPoints K p m R).symm f).toAdd.val =
      ((Spec.mapMulEquiv (R := K) (S := infinitesimalAdditiveCoordinateRing K p m)
        (T := R)).symm f).ofConv (infinitesimalAdditiveCoordinate K p m) := rfl

/-- The group-valued functor of nilpotent elements in Milne's *Algebraic Groups*,
item 2.5, is represented by the quotient Hopf algebra's affine group scheme;
here the base may be any commutative ring of prime characteristic. -/
@[expose] def infinitesimalAdditivePointsIso :
    infinitesimalAdditiveFunctor K p m ≅ infinitesimalAdditivePointsFunctor K p m :=
  NatIso.ofComponents
    (fun R ↦ (infinitesimalAdditiveMulEquivPoints K p m R).toGrpIso)
    (fun {R S} f ↦ by
      ext r
      apply Over.OverMorphism.ext
      change
        (infinitesimalAdditiveMulEquivPoints K p m S
          (.ofAdd (infinitesimalAdditiveMap K p m R f.hom r.toAdd))).left =
          ((algSpec (.of K)).map f.op).left ≫
            (infinitesimalAdditiveMulEquivPoints K p m R r).left
      rw [infinitesimalAdditiveMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (infinitesimalAdditiveMulEquivAlgHom K p m S
            (.ofAdd (infinitesimalAdditiveMap K p m R f.hom r.toAdd))).ofConv.toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (infinitesimalAdditiveMulEquivAlgHom K p m R r).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : infinitesimalAdditiveCoordinateRing K p m →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (infinitesimalAdditiveMulEquivAlgHom_naturality K p m R f.hom r.toAdd))

end AlgebraicGeometry
