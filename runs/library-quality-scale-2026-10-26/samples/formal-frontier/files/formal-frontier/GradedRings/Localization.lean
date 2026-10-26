/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Graded localizations

This file constructs the natural grading on an ordinary localization at a
submonoid of homogeneous elements.  A fraction with numerator of degree
`i + j` and denominator of degree `j` belongs to the degree-`i` component.

Public constructions retain their ordinary computational interface. The private
membership proof stays private and is inlined where exposed data require it.
-/

public section

open DirectSum

namespace GradedLocalization

universe u v w

variable {A : Type u} [CommRing A]
variable {ι : Type v} [DecidableEq ι] [AddCommGroup ι]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable (M : Submonoid A)

/-- The degree-`i` component of the localization at a homogeneous submonoid.
An element belongs to it when it has a representative `a / b` with `a` of
degree `i + j` and `b` of degree `j` for some `j`. -/
@[expose] def component (i : ι) : AddSubgroup (Localization M) where
  carrier := {z | ∃ (j : ι) (a : 𝒜 (i + j)) (b : 𝒜 j)
    (hb : (b : A) ∈ M), z = Localization.mk (a : A) ⟨(b : A), hb⟩}
  zero_mem' := by
    refine ⟨0, ⟨0, ?_⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩, one_mem M, ?_⟩
    · rw [add_zero]
      exact zero_mem (𝒜 i)
    · exact (Localization.mk_zero _).symm
  add_mem' := by
    rintro x y ⟨j, a, b, hb, rfl⟩ ⟨k, c, d, hd, rfl⟩
    refine ⟨j + k, ⟨(b : A) * c + (d : A) * a, ?_⟩,
      ⟨(b : A) * d, SetLike.GradedMul.mul_mem b.property d.property⟩,
      M.mul_mem hb hd, ?_⟩
    · have hbc : (b : A) * c ∈ 𝒜 (j + (i + k)) :=
        SetLike.GradedMul.mul_mem b.property c.property
      have hda : (d : A) * a ∈ 𝒜 (k + (i + j)) :=
        SetLike.GradedMul.mul_mem d.property a.property
      apply add_mem
      · simpa [add_assoc, add_comm, add_left_comm] using hbc
      · simpa [add_assoc, add_comm, add_left_comm] using hda
    · exact Localization.add_mk _ _ _ _
  neg_mem' := by
    rintro x ⟨j, a, b, hb, rfl⟩
    refine ⟨j, ⟨-a, neg_mem a.property⟩, b, hb, ?_⟩
    exact Localization.neg_mk _ _

theorem mk_mem_component {i j : ι} (a : 𝒜 (i + j)) (b : 𝒜 j)
    (hb : (b : A) ∈ M) :
    Localization.mk (a : A) ⟨(b : A), hb⟩ ∈ component (𝒜 := 𝒜) M i :=
  ⟨j, a, b, hb, rfl⟩

theorem algebraMap_mem_component {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    algebraMap A (Localization M) a ∈ component (𝒜 := 𝒜) M i := by
  let a' : 𝒜 (i + 0) := ⟨a, by
    rw [add_zero]
    exact ha⟩
  refine ⟨0, a', ⟨1, SetLike.one_mem_graded 𝒜⟩, one_mem M, ?_⟩
  exact (Localization.mk_one_eq_algebraMap a).symm

/-- The localized components are closed under graded multiplication. -/
instance componentGradedMonoid : SetLike.GradedMonoid (component (𝒜 := 𝒜) M) where
  one_mem := by
    refine ⟨0, ⟨1, ?_⟩, ⟨1, SetLike.one_mem_graded 𝒜⟩, one_mem M, ?_⟩
    · simpa using SetLike.one_mem_graded 𝒜
    · simp
  mul_mem i k x y hx hy := by
    rcases hx with ⟨j, a, b, hb, rfl⟩
    rcases hy with ⟨l, c, d, hd, rfl⟩
    refine ⟨j + l, ⟨(a : A) * c, ?_⟩,
      ⟨(b : A) * d, SetLike.GradedMul.mul_mem b.property d.property⟩,
      M.mul_mem hb hd, ?_⟩
    · have hac : (a : A) * c ∈ 𝒜 ((i + j) + (k + l)) :=
        SetLike.GradedMul.mul_mem a.property c.property
      simpa [add_assoc, add_comm, add_left_comm] using hac
    · exact Localization.mk_mul _ _ _ _

/-- The degree-zero localized component as a subring of the ordinary
localization. -/
@[expose] def zeroComponent : Subring (Localization M) where
  carrier := component (𝒜 := 𝒜) M 0
  zero_mem' := (component (𝒜 := 𝒜) M 0).zero_mem
  add_mem' := (component (𝒜 := 𝒜) M 0).add_mem
  neg_mem' := (component (𝒜 := 𝒜) M 0).neg_mem
  one_mem' := SetLike.one_mem_graded (component (𝒜 := 𝒜) M)
  mul_mem' {x y} hx hy := by
    change x * y ∈ component (𝒜 := 𝒜) M 0
    simpa only [zero_add] using
      (SetLike.GradedMul.mul_mem hx hy :
        x * y ∈ component (𝒜 := 𝒜) M (0 + 0))

private theorem homogeneousLocalization_val_mem_zeroComponent
    (x : HomogeneousLocalization 𝒜 M) :
    x.val ∈ zeroComponent (𝒜 := 𝒜) M := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  let a : 𝒜 (0 + c.deg) := ⟨c.num, by
    rw [zero_add]
    exact c.num.property⟩
  exact ⟨c.deg, a, c.den, c.den_mem, rfl⟩

/-- The natural map from the homogeneous localization to the degree-zero
component of the ordinary localization. -/
@[expose] def toZeroComponent :
    HomogeneousLocalization 𝒜 M →+* zeroComponent (𝒜 := 𝒜) M where
  toFun x := ⟨x.val, by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
    let a : 𝒜 (0 + c.deg) := ⟨c.num, by
      rw [zero_add]
      exact c.num.property⟩
    exact ⟨c.deg, a, c.den, c.den_mem, rfl⟩⟩
  map_zero' := by ext; exact HomogeneousLocalization.val_zero
  map_one' := by ext; exact HomogeneousLocalization.val_one
  map_add' x y := by ext; exact HomogeneousLocalization.val_add x y
  map_mul' x y := by ext; exact HomogeneousLocalization.val_mul x y

private def toZeroComponent_privateConstruction :
    HomogeneousLocalization 𝒜 M →+* zeroComponent (𝒜 := 𝒜) M where
  toFun x := ⟨x.val, homogeneousLocalization_val_mem_zeroComponent 𝒜 M x⟩
  map_zero' := by ext; exact HomogeneousLocalization.val_zero
  map_one' := by ext; exact HomogeneousLocalization.val_one
  map_add' x y := by ext; exact HomogeneousLocalization.val_add x y
  map_mul' x y := by ext; exact HomogeneousLocalization.val_mul x y

private theorem toZeroComponent_eq_privateConstruction :
    toZeroComponent (𝒜 := 𝒜) M = toZeroComponent_privateConstruction 𝒜 M :=
  rfl

theorem toZeroComponent_injective :
    Function.Injective (toZeroComponent (𝒜 := 𝒜) M) := by
  intro x y hxy
  apply HomogeneousLocalization.val_injective M
  exact congrArg Subtype.val hxy

theorem toZeroComponent_surjective :
    Function.Surjective (toZeroComponent (𝒜 := 𝒜) M) := by
  rintro ⟨x, hx⟩
  rcases hx with ⟨j, a, b, hb, rfl⟩
  have ha : (a : A) ∈ 𝒜 j := by
    simpa only [zero_add] using a.property
  let a' : 𝒜 j := ⟨a, ha⟩
  refine ⟨HomogeneousLocalization.mk
    ⟨j, a', b, hb⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- The degree-zero part of the full graded localization agrees with mathlib's
`HomogeneousLocalization`.  The forward map is induced by
`HomogeneousLocalization.val`. -/
@[expose] noncomputable def homogeneousLocalizationEquivZeroComponent :
    HomogeneousLocalization 𝒜 M ≃+* zeroComponent (𝒜 := 𝒜) M :=
  RingEquiv.ofBijective (toZeroComponent (𝒜 := 𝒜) M)
    ⟨toZeroComponent_injective 𝒜 M, toZeroComponent_surjective 𝒜 M⟩

variable (hM : M ≤ SetLike.homogeneousSubmonoid 𝒜)

/-- The degree-`i` part of a localized fraction.  A denominator degree is
chosen, and the numerator is projected to degree `i` plus that denominator
degree.  The localization relation makes the result independent of the
chosen representative, even when homogeneous denominators are zero divisors. -/
@[expose] noncomputable def projectionFun (i : ι) (x : Localization M) : Localization M :=
  x.liftOn
    (fun a s ↦ Localization.mk
      (DirectSum.decompose 𝒜 a (i + (hM s.2).choose) : A) s)
    fun {a₁ a₂} {s₁ s₂} h ↦ by
      rw [Localization.mk_eq_mk_iff]
      rw [Localization.r_iff_exists] at h ⊢
      obtain ⟨s, hs⟩ := h
      refine ⟨s, ?_⟩
      replace hs := congr((DirectSum.decompose 𝒜 $hs
        ((hM s.2).choose + ((hM s₂.2).choose +
          (i + (hM s₁.2).choose))) : A))
      simp_rw [DirectSum.decompose_mul,
        DirectSum.decompose_of_mem _ (hM (Subtype.prop _)).choose_spec,
        DirectSum.coe_of_mul_apply_add] at hs
      rw [show (hM s₂.2).choose + (i + (hM s₁.2).choose) =
        (hM s₁.2).choose + (i + (hM s₂.2).choose) by ac_rfl,
        DirectSum.coe_of_mul_apply_add] at hs
      exact hs

theorem projectionFun_mk (i : ι) {a : A} {s : M} {j : ι}
    (hs : (s : A) ∈ 𝒜 j) :
    projectionFun 𝒜 M hM i (Localization.mk a s) =
      Localization.mk (DirectSum.decompose 𝒜 a (i + j) : A) s := by
  by_cases h0 : 0 ∈ M
  · exact (IsLocalization.subsingleton (S := Localization M) h0).elim _ _
  · have hj : (hM s.2).choose = j :=
      DirectSum.degree_eq_of_mem_mem 𝒜 (hM s.2).choose_spec hs (by grind)
    change Localization.mk
      (DirectSum.decompose 𝒜 a (i + (hM s.2).choose) : A) s = _
    rw [hj]

/-- Projection onto degree `i` in a localization at homogeneous elements. -/
@[expose] noncomputable def projection (i : ι) : Localization M →+ Localization M where
  toFun := projectionFun 𝒜 M hM i
  map_zero' := by
    rw [← Localization.mk_zero (1 : M), projectionFun_mk 𝒜 M hM i
      (SetLike.one_mem_graded 𝒜)]
    simp
  map_add' x y := by
    refine Localization.induction_on₂ x y fun c d ↦ ?_
    obtain ⟨j, hcj⟩ := hM c.2.2
    obtain ⟨k, hdk⟩ := hM d.2.2
    rw [Localization.add_mk, projectionFun_mk 𝒜 M hM i hcj,
      projectionFun_mk 𝒜 M hM i hdk,
      projectionFun_mk 𝒜 M hM i
        (SetLike.GradedMul.mul_mem hcj hdk), Localization.add_mk]
    congr 1
    simp only [decompose_add, decompose_mul, DirectSum.add_apply, AddMemClass.coe_add,
      DirectSum.decompose_of_mem _ hcj, DirectSum.decompose_of_mem _ hdk]
    rw [show i + (j + k) = j + (i + k) by ac_rfl,
      DirectSum.coe_of_mul_apply_add]
    rw [show j + (i + k) = k + (i + j) by ac_rfl,
      DirectSum.coe_of_mul_apply_add]

theorem projection_mem_component (i : ι) (x : Localization M) :
    projection 𝒜 M hM i x ∈ component (𝒜 := 𝒜) M i := by
  refine Localization.induction_on x fun c ↦ ?_
  obtain ⟨j, hcj⟩ := hM c.2.2
  change projectionFun 𝒜 M hM i (Localization.mk c.1 c.2) ∈ _
  rw [projectionFun_mk 𝒜 M hM i hcj]
  exact ⟨j, DirectSum.decompose 𝒜 c.1 (i + j),
    ⟨c.2, hcj⟩, c.2.2, rfl⟩

theorem projection_eq_self_of_mem (i : ι) {x : Localization M}
    (hx : x ∈ component (𝒜 := 𝒜) M i) : projection 𝒜 M hM i x = x := by
  rcases hx with ⟨j, a, b, hb, rfl⟩
  change projectionFun 𝒜 M hM i
      (Localization.mk (a : A) ⟨(b : A), hb⟩) = _
  rw [projectionFun_mk 𝒜 M hM i b.property,
    DirectSum.decompose_of_mem_same 𝒜 a.property]

theorem projection_eq_zero_of_mem {i k : ι} (hik : i ≠ k)
    {x : Localization M} (hx : x ∈ component (𝒜 := 𝒜) M k) :
    projection 𝒜 M hM i x = 0 := by
  rcases hx with ⟨j, a, b, hb, rfl⟩
  change projectionFun 𝒜 M hM i
      (Localization.mk (a : A) ⟨(b : A), hb⟩) = _
  rw [projectionFun_mk 𝒜 M hM i b.property,
    DirectSum.decompose_of_mem_ne 𝒜 a.property (by simpa using hik.symm),
    Localization.mk_zero]

theorem projection_coe (i : ι)
    (z : ⨁ k, component (𝒜 := 𝒜) M k) :
    projection 𝒜 M hM i
        (DirectSum.coeAddMonoidHom (component (𝒜 := 𝒜) M) z) = z i := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of k y =>
      rw [DirectSum.coeAddMonoidHom_of]
      by_cases hik : i = k
      · subst k
        rw [projection_eq_self_of_mem 𝒜 M hM i y.property]
        simp
      · rw [projection_eq_zero_of_mem 𝒜 M hM hik y.property]
        have hki : k ≠ i := fun h ↦ hik h.symm
        simp [DirectSum.of_apply, hki]
  | add x y hx hy => simp [hx, hy]

include hM in
theorem coe_injective :
    Function.Injective
      (DirectSum.coeAddMonoidHom (component (𝒜 := 𝒜) M)) := by
  intro x y hxy
  apply DirectSum.ext
  intro i
  apply Subtype.ext
  have hi := congrArg (fun z ↦ projection 𝒜 M hM i z) hxy
  rw [projection_coe 𝒜 M hM i, projection_coe 𝒜 M hM i] at hi
  exact hi

private theorem mk_mem_range (a : A) (s : M) {j : ι}
    (hs : (s : A) ∈ 𝒜 j) :
    Localization.mk a s ∈
      Set.range (DirectSum.coeAddMonoidHom (component (𝒜 := 𝒜) M)) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, (Localization.mk_zero s).symm⟩
  | @homogeneous k a =>
      let a' : 𝒜 ((k - j) + j) := ⟨a, by
        rw [sub_add_cancel]
        exact a.property⟩
      let s' : 𝒜 j := ⟨s, hs⟩
      have hm : Localization.mk (a : A) s ∈
          component (𝒜 := 𝒜) M (k - j) :=
        ⟨j, a', s', s.2, rfl⟩
      refine ⟨DirectSum.of _ (k - j)
        ⟨Localization.mk (a : A) s, hm⟩, ?_⟩
      exact DirectSum.coeAddMonoidHom_of _ _ _
  | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      refine ⟨x + y, ?_⟩
      rw [map_add, hx, hy, Localization.add_mk_self]

include hM in
theorem coe_surjective :
    Function.Surjective
      (DirectSum.coeAddMonoidHom (component (𝒜 := 𝒜) M)) := by
  intro x
  refine Localization.induction_on x fun c ↦ ?_
  obtain ⟨j, hcj⟩ := hM c.2.2
  exact mk_mem_range 𝒜 M c.1 c.2 hcj

include hM in
/-- The localized homogeneous components form an internal direct sum. -/
theorem isInternal : DirectSum.IsInternal (component (𝒜 := 𝒜) M) :=
  ⟨coe_injective 𝒜 M hM, coe_surjective 𝒜 M hM⟩

/-- The natural direct-sum decomposition of a localization at homogeneous
elements. -/
@[expose, instance_reducible]
noncomputable def decomposition :
    DirectSum.Decomposition (component (𝒜 := 𝒜) M) :=
  (isInternal 𝒜 M hM).chooseDecomposition

/-- The natural grading on an ordinary localization at a homogeneous
submonoid. -/
@[expose, instance_reducible]
noncomputable def gradedRing : GradedRing (component (𝒜 := 𝒜) M) where
  toGradedMonoid := componentGradedMonoid (𝒜 := 𝒜) M
  toDecomposition := decomposition 𝒜 M hM

end GradedLocalization
