/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The counit range and its action on the coalgebra

The range of the counit of an `R`-coalgebra is an ideal of the commutative
semiring `R`. Its square equals itself: the fact that the counit is a
coalgebra homomorphism expresses each counit value as a sum of products of
counit values. Tensor induction proves membership in the square without
any freeness or finiteness assumption on the coalgebra.
For a tensor product, the counit range is the product of the two scalar ideals,
and its counit is surjective exactly when both factor counits are surjective.
These two statements require only `CoalgebraStruct` on each factor, not the
coalgebra identities. The idempotence and scalar-action results do use those
identities. For a coalgebra satisfying them, the counit is zero exactly when
the coalgebra is subsingleton; in particular, orthogonal scalar supports give
a zero tensor product of coalgebras.

The counit range also generates the whole coalgebra under scalar multiplication:
every element is a sum of terms `ε(x) • y` by the left counit identity. Thus its
action on the top submodule is top, even when the counit range is a proper ideal.
The counit range detects equality of scalar actions: two scalars act identically
on the coalgebra exactly when they act identically on its counit range. Hence the
scalar action on the coalgebra is faithful if and only if its action on the
counit range is faithful. No finiteness or freeness assumption is required.

For a nontrivial coalgebra whose underlying module is free, a basis coordinate
maps the spanning identity to the scalar semiring, so the counit is surjective.
Neither a finite basis nor a ring or field structure on the scalars is required.

Over a commutative ring, a finitely generated counit image also equals the whole
ring when the scalar action on the coalgebra is faithful. The finiteness premise
concerns only the image ideal, not the underlying module. Mathlib's theorem on
finitely generated idempotent ideals supplies an idempotent generator; the counit
identity makes it act identically, and faithfulness identifies it with one.
Faithfulness alone does not give this conclusion without finite generation of
the image ideal.

Over a commutative ring, the underlying module is faithfully flat exactly when
it is flat and its counit is surjective, or equivalently has range the whole
scalar ring. In the forward direction, the counit-law action on the top submodule
and Mathlib's ideal-top reflection criterion make the range the whole ring.
Conversely, CoherentModules' general constructor for a flat module surjecting onto
a faithfully flat module applies to the counit, since the scalar ring is faithfully
flat over itself. No finite generation or nontriviality is required; flatness
concerns the coalgebra carrier, not a separate scalar extension.

## References

Mathlib supplies the counit coalgebra homomorphism, tensor induction,
free-module bases, ideal multiplication and submodule scalar action used here.
The tensor-product range formula uses Mathlib's `TensorProduct.range_map` and
`Submodule.mulMap_range`; the surjectivity criterion uses `LinearMap.range_eq_top`,
`Ideal.isUnit_iff` and `IsUnit.mul_iff`. Equality of scalar actions uses the
surjectivity of `LinearMap.rangeRestrict`, linearity and the left counit identity.
The finitely generated faithful-action criterion reuses Mathlib's
`Ideal.isIdempotentElem_iff_of_fg`, singleton-ideal scalar action and
`FaithfulSMul.eq_of_smul_eq_smul`. The faithfully flat criterion combines
`counit_range_smul_top` with Mathlib's
`Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top`. Its converse uses
CoherentModules' public `Module.FaithfullyFlat.of_surjective` from
`CoherentModules.RingTheory.Flat.FaithfullyFlat` with Mathlib's
`Module.FaithfullyFlat.self`. The generic constructor transports ideal scalar
action using Mathlib's `Submodule.map_smul''`, `Submodule.map_top` and
`LinearMap.range_eq_top`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Coalgebra

section CommSemiring

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The scalar ideal given by the range of the counit is idempotent. -/
@[simp] theorem counit_range_mul_self :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) *
      LinearMap.range (counit (R := R) (A := C)) =
    LinearMap.range (counit (R := R) (A := C)) := by
  let I : Ideal R := LinearMap.range (counit (R := R) (A := C))
  apply le_antisymm Ideal.mul_le_right
  rintro r ⟨c, rfl⟩
  have h (t : C ⊗[R] C) :
      _root_.TensorProduct.lid R R
        (_root_.TensorProduct.map (counit (R := R)) (counit (R := R)) t) ∈
        I * I := by
    induction t using _root_.TensorProduct.inductionOn with
    | tmul x y =>
      simpa only [_root_.TensorProduct.map_tmul, _root_.TensorProduct.lid_tmul, smul_eq_mul] using
        (Ideal.mul_mem_mul (LinearMap.mem_range_self (counit (R := R)) x)
          (LinearMap.mem_range_self (counit (R := R)) y))
    | add x y hx hy =>
      simpa only [map_add] using (I * I).add_mem hx hy
  have hε : _root_.TensorProduct.map (counit (R := R)) (counit (R := R)) (comul c) =
      (1 : R) ⊗ₜ[R] counit (R := R) c := by
    simpa only [CoalgHom.toLinearMap_eq_coe, counitCoalgHom_toLinearMap,
      LinearMap.comp_apply, CommSemiring.comul_apply] using
      (LinearMap.congr_fun (counitCoalgHom R C).map_comp_comul c)
  simpa only [hε, _root_.TensorProduct.lid_tmul, one_smul] using h (comul c)

/-- The counit range generates the whole coalgebra under scalar multiplication.
This does not require the counit range to be the whole scalar semiring. -/
@[simp] theorem counit_range_smul_top :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) •
      (⊤ : Submodule R C) = ⊤ := by
  let I : Ideal R := LinearMap.range (counit (R := R) (A := C))
  apply top_unique
  intro c _
  have h (t : C ⊗[R] C) :
      _root_.TensorProduct.lid R C ((counit (R := R)).rTensor C t) ∈
        I • (⊤ : Submodule R C) := by
    induction t using _root_.TensorProduct.inductionOn with
    | tmul x y =>
      simpa only [LinearMap.rTensor_tmul, _root_.TensorProduct.lid_tmul] using
        (Submodule.smul_mem_smul (LinearMap.mem_range_self (counit (R := R)) x)
          (Submodule.mem_top : y ∈ (⊤ : Submodule R C)))
    | add x y hx hy =>
      simpa only [map_add] using (I • (⊤ : Submodule R C)).add_mem hx hy
  simpa only [rTensor_counit_comul, _root_.TensorProduct.lid_tmul, one_smul] using h (comul c)

/-- Two scalars act identically on a coalgebra if and only if they act identically
on the range of its counit. This holds over a commutative semiring without any
finiteness or freeness assumption. -/
theorem smul_eq_smul_iff_on_counit_range {r s : R} :
    (∀ c : C, r • c = s • c) ↔
      ∀ x : LinearMap.range (counit (R := R) (A := C)), r • x = s • x := by
  constructor
  · intro h x
    obtain ⟨c, rfl⟩ := (counit (R := R) (A := C)).surjective_rangeRestrict x
    simpa only [map_smul] using congrArg (counit (R := R) (A := C)).rangeRestrict (h c)
  · intro h c
    have hε (x : C) : r * counit (R := R) x = s * counit (R := R) x := by
      simpa only [Submodule.coe_smul, smul_eq_mul, LinearMap.codRestrict_apply] using
        congrArg Subtype.val (h ((counit (R := R) (A := C)).rangeRestrict x))
    have ht (t : C ⊗[R] C) :
        r • _root_.TensorProduct.lid R C ((counit (R := R)).rTensor C t) =
          s • _root_.TensorProduct.lid R C ((counit (R := R)).rTensor C t) := by
      induction t using _root_.TensorProduct.inductionOn with
      | tmul x y =>
        simpa only [LinearMap.rTensor_tmul, _root_.TensorProduct.lid_tmul, ← mul_smul] using
          congrArg (fun a : R ↦ a • y) (hε x)
      | add x y hx hy =>
        simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy
    simpa only [rTensor_counit_comul, _root_.TensorProduct.lid_tmul, one_smul] using ht (comul c)

/-- The scalar action on a coalgebra is faithful if and only if the scalar action
on the range of its counit is faithful. -/
theorem faithfulSMul_iff_counit_range :
    FaithfulSMul R C ↔ FaithfulSMul R (LinearMap.range (counit (R := R) (A := C))) := by
  constructor
  · intro h
    exact ⟨fun {r s} hrs ↦ h.eq_of_smul_eq_smul
      ((smul_eq_smul_iff_on_counit_range R C (r := r) (s := s)).mpr hrs)⟩
  · intro h
    exact ⟨fun {r s} hrs ↦ h.eq_of_smul_eq_smul
      ((smul_eq_smul_iff_on_counit_range R C (r := r) (s := s)).mp hrs)⟩

/-- The counit range of a nontrivial coalgebra with free underlying module is the
whole scalar semiring. No finiteness assumption on a basis is needed. -/
@[simp] theorem counit_range_eq_top_of_free [Module.Free R C] [Nontrivial C] :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis R C
  let i : Module.Free.ChooseBasisIndex R C := Classical.choice inferInstance
  have hcoord : LinearMap.range (b.coord i) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro r
    refine ⟨r • b i, ?_⟩
    simp [Module.Basis.coord_apply]
  have h := congrArg (Submodule.map (b.coord i)) (counit_range_smul_top R C)
  rw [Submodule.map_smul'', Submodule.map_top, hcoord, Ideal.smul_eq_mul,
    Ideal.mul_top] at h
  exact h

/-- The counit of a nontrivial coalgebra with free underlying module is surjective
onto its commutative scalar semiring. -/
theorem counit_surjective_of_free [Module.Free R C] [Nontrivial C] :
    Function.Surjective (counit (R := R) (A := C)) :=
  LinearMap.range_eq_top.mp (counit_range_eq_top_of_free R C)

/-- The counit is zero exactly when the coalgebra is subsingleton.
The left counit identity gives this without any freeness assumption. -/
@[simp] theorem counit_eq_zero_iff :
    counit (R := R) (A := C) = 0 ↔ Subsingleton C := by
  constructor
  · intro h
    have hz (c : C) : c = 0 := by
      have hc := congrArg (_root_.TensorProduct.lid R C) (rTensor_counit_comul (R := R) c)
      simpa only [h, LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero,
        _root_.TensorProduct.lid_tmul, one_smul] using hc.symm
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · intro h
    let := h
    ext c
    rw [Subsingleton.elim c 0]
    simp

end CommSemiring

section TensorProduct

variable (R : Type u) (C : Type v) (D : Type w)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
variable [AddCommMonoid D] [Module R D] [CoalgebraStruct R D]

/-- The scalar ideal given by the counit range of a tensor product is the product
of the two counit ranges. Only the structure maps on each factor are required,
not the coalgebra identities, freeness or finiteness. -/
theorem counit_range_tensorProduct :
    (LinearMap.range (counit (R := R) (A := C ⊗[R] D)) : Ideal R) =
      (LinearMap.range (counit (R := R) (A := C)) : Ideal R) *
        LinearMap.range (counit (R := R) (A := D)) := by
  let I : Ideal R := LinearMap.range (counit (R := R) (A := C))
  let J : Ideal R := LinearMap.range (counit (R := R) (A := D))
  have hε : counit (R := R) (A := C ⊗[R] D) =
      Submodule.mulMap I J ∘ₗ
        _root_.TensorProduct.map (counit (R := R) (A := C)).rangeRestrict
          (counit (R := R) (A := D)).rangeRestrict := by
    ext c d
    simp [I, J, mul_comm]
  have hrange : LinearMap.range
      (_root_.TensorProduct.map (counit (R := R) (A := C)).rangeRestrict
        (counit (R := R) (A := D)).rangeRestrict) = ⊤ := by
    simp only [_root_.TensorProduct.range_map, LinearMap.range_rangeRestrict,
      _root_.TensorProduct.map₂_mk_top_top_eq_top]
  rw [hε, LinearMap.range_comp, hrange, Submodule.map_top]
  exact Submodule.mulMap_range I J

/-- The tensor-product counit is surjective exactly when both factor counits are
surjective. Only `CoalgebraStruct` on each factor is required. -/
theorem counit_surjective_tensorProduct_iff :
    Function.Surjective (counit (R := R) (A := C ⊗[R] D)) ↔
      Function.Surjective (counit (R := R) (A := C)) ∧
        Function.Surjective (counit (R := R) (A := D)) := by
  rw [← LinearMap.range_eq_top, counit_range_tensorProduct, ← Ideal.isUnit_iff,
    IsUnit.mul_iff, Ideal.isUnit_iff, Ideal.isUnit_iff,
    LinearMap.range_eq_top, LinearMap.range_eq_top]

end TensorProduct

section CommRing

variable (R : Type u) (C : Type v)
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [FaithfulSMul R C]

open scoped Pointwise in
/-- A finitely generated counit image is the whole scalar ring if the scalar action
on the coalgebra is faithful. Only the image ideal needs to be finitely generated;
no finiteness, freeness or projectivity of the underlying module is required. -/
theorem counit_range_eq_top_of_faithfulSMul_of_fg
    (hfg : (LinearMap.range (counit (R := R) (A := C)) : Ideal R).FG) :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) = ⊤ := by
  obtain ⟨e, he, hspan⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg
      (LinearMap.range (counit (R := R) (A := C)) : Ideal R) hfg).mp
        (counit_range_mul_self R C)
  rw [Ideal.submodule_span_eq] at hspan
  have htop : e • (⊤ : Submodule R C) = ⊤ := by
    rw [← Submodule.ideal_span_singleton_smul, ← hspan]
    exact counit_range_smul_top R C
  have he_smul (c : C) : e • c = c := by
    have hc : c ∈ e • (⊤ : Submodule R C) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists c e ⊤).mp hc
    calc
      e • c = e • (e • y) := congrArg (e • ·) hy.symm
      _ = (e * e) • y := (mul_smul e e y).symm
      _ = e • y := by rw [he.eq]
      _ = c := hy
  have he_one : e = 1 := eq_of_smul_eq_smul (α := C) fun c ↦ by
    rw [he_smul c, one_smul]
  simpa only [he_one, Ideal.span_singleton_one] using hspan

/-- The counit is surjective for a coalgebra with faithful scalar action and
finitely generated counit image ideal. The underlying module may be infinite. -/
theorem counit_surjective_of_faithfulSMul_of_fg
    (hfg : (LinearMap.range (counit (R := R) (A := C)) : Ideal R).FG) :
    Function.Surjective (counit (R := R) (A := C)) :=
  LinearMap.range_eq_top.mp (counit_range_eq_top_of_faithfulSMul_of_fg R C hfg)

end CommRing

section CommRingFaithfullyFlat

variable (R : Type u) (C : Type v)
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]
variable [Module.FaithfullyFlat R C]

/-- The counit range is the whole scalar ring when the underlying module is
faithfully flat. Mathlib's ideal-top reflection applies to the counit-law action. -/
@[simp] theorem counit_range_eq_top_of_faithfullyFlat :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) = ⊤ := by
  exact ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top R C).mp inferInstance).2 _
    (counit_range_smul_top R C)

/-- The counit is surjective when the underlying module is faithfully flat. -/
theorem counit_surjective_of_faithfullyFlat :
    Function.Surjective (counit (R := R) (A := C)) :=
  LinearMap.range_eq_top.mp (counit_range_eq_top_of_faithfullyFlat R C)

end CommRingFaithfullyFlat

/-- The underlying module of a coalgebra over a commutative ring is faithfully flat
exactly when it is flat and its counit is surjective. Flatness is a separate
module-theoretic requirement. -/
theorem faithfullyFlat_iff_flat_and_counit_surjective
    (R : Type u) (C : Type v)
    [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C] :
    Module.FaithfullyFlat R C ↔
      Module.Flat R C ∧
        Function.Surjective (Coalgebra.counit (R := R) (A := C)) := by
  constructor
  · intro hFF
    let := hFF
    exact ⟨inferInstance, counit_surjective_of_faithfullyFlat R C⟩
  · rintro ⟨hflat, hsurj⟩
    let : Module.Flat R C := hflat
    exact Module.FaithfullyFlat.of_surjective (counit (R := R) (A := C)) hsurj

/-- The underlying module of a coalgebra over a commutative ring is faithfully flat
exactly when it is flat and the scalar ideal given by its counit range is the
whole ring. -/
theorem faithfullyFlat_iff_flat_and_counit_range_eq_top
    (R : Type u) (C : Type v)
    [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C] :
    Module.FaithfullyFlat R C ↔
      Module.Flat R C ∧
        (LinearMap.range (Coalgebra.counit (R := R) (A := C)) : Ideal R) = ⊤ := by
  simpa only [LinearMap.range_eq_top] using
    (faithfullyFlat_iff_flat_and_counit_surjective R C)

end Coalgebra
