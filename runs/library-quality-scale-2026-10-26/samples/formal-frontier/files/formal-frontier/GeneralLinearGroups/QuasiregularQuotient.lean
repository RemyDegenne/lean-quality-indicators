/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.CongruenceSubgroup
public import GeneralLinearGroups.MatrixQuasiregular
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Tactic.NoncommRing

/-!
# General linear groups over quasi-regular quotients

This file proves that quotienting an arbitrary ring by a quasi-regular
two-sided ideal induces a surjection on finite general linear groups. The proof
lifts a matrix and its inverse entrywise, then uses quasi-regularity of the
corresponding matrix ideal to show that both ordered products are units.
The scalar interface gives unit reflection as Mathlib's `IsLocalHom` for a
surjective ring homomorphism with quasi-regular two-sided kernel. It lifts the
inverse of a unit image and applies the same ordered-product argument, using
Mathlib's kernel congruence API to keep subtraction in the source ring. The
target need only be a semiring. The complementary scalar statements assert that
unit reflection implies quasi-regularity of the kernel, with equivalence for
surjective homomorphisms.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

private theorem isUnit_of_mul_isUnit_and_isUnit_mul
    {M : Type w} [Monoid M] {a b : M}
    (hab : IsUnit (a * b)) (hba : IsUnit (b * a)) : IsUnit a := by
  let uab : Mˣ := hab.unit
  let uba : Mˣ := hba.unit
  let r : M := b * (↑(uab⁻¹) : M)
  let l : M := (↑(uba⁻¹) : M) * b
  have har : a * r = 1 := by
    change a * (b * (↑(uab⁻¹) : M)) = 1
    rw [← mul_assoc, ← hab.unit_spec]
    exact Units.val_inv uab
  have hla : l * a = 1 := by
    change (↑(uba⁻¹) : M) * b * a = 1
    rw [mul_assoc, ← hba.unit_spec]
    exact Units.inv_val uba
  have hlr : l = r := by
    calc
      l = l * 1 := by rw [mul_one]
      _ = l * (a * r) := by rw [har]
      _ = (l * a) * r := (mul_assoc l a r).symm
      _ = r := by rw [hla, one_mul]
  refine ⟨⟨a, r, har, ?_⟩, rfl⟩
  rw [← hlr]
  exact hla

private theorem mem_matrix_of_mapMatrix_quotient_eq_zero
    {R : Type u} [Ring R]
    {n : Type v} [Fintype n] [DecidableEq n]
    (I : TwoSidedIdeal R) (A : Matrix n n R)
    (hA : (Ideal.Quotient.mk I.asIdeal).mapMatrix A = 0) :
    A ∈ I.matrix n := by
  rw [TwoSidedIdeal.mem_matrix]
  intro i j
  apply TwoSidedIdeal.mem_asIdeal.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hij := congrFun (congrFun hA i) j
  simpa using hij

/-- A matrix over a ring is a unit if its image modulo a quasi-regular
two-sided ideal is a unit. The finite index type may be empty. -/
theorem isUnit_of_mapMatrix_quotient_isUnit
    {R : Type u} [Ring R]
    {n : Type v} [Fintype n] [DecidableEq n]
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) (A : Matrix n n R)
    (hA : IsUnit ((Ideal.Quotient.mk I.asIdeal).mapMatrix A)) : IsUnit A := by
  let f : R →+* R ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  let g : GL n (R ⧸ I.asIdeal) := hA.unit
  let B : Matrix n n R := liftMatrix f hf
    ((g⁻¹ : GL n (R ⧸ I.asIdeal)) : Matrix n n (R ⧸ I.asIdeal))
  have hmapA : f.mapMatrix A = (g : Matrix n n (R ⧸ I.asIdeal)) := by
    exact hA.unit_spec.symm
  have hmapB : f.mapMatrix B =
      ((g⁻¹ : GL n (R ⧸ I.asIdeal)) : Matrix n n (R ⧸ I.asIdeal)) := by
    exact mapMatrix_liftMatrix f hf _
  have hABzero : f.mapMatrix (A * B - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hmapA, hmapB]
    exact sub_eq_zero.mpr (Units.val_inv g)
  have hBAzero : f.mapMatrix (B * A - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hmapB, hmapA]
    exact sub_eq_zero.mpr (Units.inv_val g)
  have hABmem : A * B - 1 ∈ I.matrix n :=
    mem_matrix_of_mapMatrix_quotient_eq_zero I _ hABzero
  have hBAmem : B * A - 1 ∈ I.matrix n :=
    mem_matrix_of_mapMatrix_quotient_eq_zero I _ hBAzero
  have hMatrixUnits :
      ∀ X : Matrix n n R, X ∈ I.matrix n → IsUnit (1 + X) :=
    (I.matrix n).isQuasiregular_iff_forall_isUnit_one_add.mp (hI.matrix n)
  have hABunit : IsUnit (A * B) := by
    have h := hMatrixUnits (A * B - 1) hABmem
    have heq : 1 + (A * B - 1) = A * B := by noncomm_ring
    rw [heq] at h
    exact h
  have hBAunit : IsUnit (B * A) := by
    have h := hMatrixUnits (B * A - 1) hBAmem
    have heq : 1 + (B * A - 1) = B * A := by noncomm_ring
    rw [heq] at h
    exact h
  exact isUnit_of_mul_isUnit_and_isUnit_mul hABunit hBAunit

/-- A quasi-regular two-sided ideal induces a surjection on general linear
groups after quotienting. The finite index type may be empty. -/
theorem mapRingHom_quotient_surjective
    {R : Type u} [Ring R]
    {n : Type v} [Fintype n] [DecidableEq n]
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) :
    Function.Surjective (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
      GL n R →* GL n (R ⧸ I.asIdeal)) := by
  intro g
  let f : R →+* R ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  let A : Matrix n n R := liftMatrix f hf (g : Matrix n n (R ⧸ I.asIdeal))
  have hmapA : f.mapMatrix A = (g : Matrix n n (R ⧸ I.asIdeal)) := by
    exact mapMatrix_liftMatrix f hf _
  have hmapAunit : IsUnit (f.mapMatrix A) := by
    rw [hmapA]
    exact g.isUnit
  have hAunit : IsUnit A :=
    isUnit_of_mapMatrix_quotient_isUnit I hI A hmapAunit
  refine ⟨hAunit.unit, ?_⟩
  apply Units.ext
  change f.mapMatrix (↑hAunit.unit : Matrix n n R) =
    (g : Matrix n n (R ⧸ I.asIdeal))
  rw [hAunit.unit_spec]
  exact hmapA

/-- For a quasi-regular two-sided ideal, its general linear group maps into
the ambient general linear group as the kernel of the surjective reduction
map.  These are the injective, exact, and surjective assertions of the
associated short exact sequence. -/
theorem idealGeneralLinearGroupToRing_shortExact
    {R : Type u} [Ring R]
    {n : Type v} [Fintype n] [DecidableEq n]
    (I : TwoSidedIdeal R) (hI : I.IsQuasiregular) :
    Function.Injective (idealGeneralLinearGroupToRing (n := n) I) ∧
      Function.MulExact (idealGeneralLinearGroupToRing (n := n) I)
        (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
          GL n R →* GL n (R ⧸ I.asIdeal)) ∧
      Function.Surjective (mapRingHom (Ideal.Quotient.mk I.asIdeal) :
        GL n R →* GL n (R ⧸ I.asIdeal)) :=
  ⟨idealGeneralLinearGroupToRing_injective I,
    idealGeneralLinearGroupToRing_mulExact I,
    mapRingHom_quotient_surjective I hI⟩

end Matrix.GeneralLinearGroup

namespace RingHom

universe u v

private theorem isUnit_of_map_eq_one_of_isQuasiregular_ker
    {R : Type u} {S : Type v} [Ring R] [Semiring S]
    (f : R →+* S) (hker : (TwoSidedIdeal.ker f).IsQuasiregular)
    {x : R} (hx : f x = 1) : IsUnit x := by
  have hxker : x - 1 ∈ TwoSidedIdeal.ker f := by
    rw [← (TwoSidedIdeal.ker f).rel_iff, TwoSidedIdeal.ker_ringCon f, map_one]
    exact hx
  have hunit := (TwoSidedIdeal.ker f).isQuasiregular_iff_forall_isUnit_one_add.mp
    hker (x - 1) hxker
  have heq : 1 + (x - 1) = x := by noncomm_ring
  rwa [heq] at hunit

/-- A surjective ring homomorphism with quasi-regular two-sided kernel reflects
units. The source may be noncommutative and the target need only be a semiring. -/
theorem isLocalHom_of_surjective_of_isQuasiregular_ker
    {R : Type u} {S : Type v} [Ring R] [Semiring S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hker : (TwoSidedIdeal.ker f).IsQuasiregular) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  let g : Sˣ := ha.unit
  have hg : (g : S) = f a := ha.unit_spec
  obtain ⟨b, hb⟩ := hf (↑(g⁻¹) : S)
  have hab : f (a * b) = 1 := by
    rw [map_mul, hb, ← hg]
    exact Units.val_inv g
  have hba : f (b * a) = 1 := by
    rw [map_mul, hb, ← hg]
    exact Units.inv_val g
  exact Matrix.GeneralLinearGroup.isUnit_of_mul_isUnit_and_isUnit_mul
    (isUnit_of_map_eq_one_of_isQuasiregular_ker f hker hab)
    (isUnit_of_map_eq_one_of_isQuasiregular_ker f hker hba)

/-- The two-sided kernel of a unit-reflecting ring homomorphism is quasi-regular.
Surjectivity is not required. The source may be noncommutative and the target
need only be a semiring. -/
theorem isQuasiregular_ker
    {R : Type u} {S : Type v} [Ring R] [Semiring S]
    (f : R →+* S) [IsLocalHom f] : (TwoSidedIdeal.ker f).IsQuasiregular := by
  apply (TwoSidedIdeal.ker f).isQuasiregular_iff_forall_isUnit_one_add.mpr
  intro x hx
  apply IsUnit.of_map f (1 + x)
  rw [map_add, map_one, (TwoSidedIdeal.mem_ker f).mp hx, add_zero]
  exact isUnit_one

/-- A surjective ring homomorphism reflects units if and only if its two-sided
kernel is quasi-regular. The source may be noncommutative and the target need
only be a semiring. -/
theorem isLocalHom_iff_isQuasiregular_ker
    {R : Type u} {S : Type v} [Ring R] [Semiring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalHom f ↔ (TwoSidedIdeal.ker f).IsQuasiregular := by
  constructor
  · intro h
    let : IsLocalHom f := h
    exact isQuasiregular_ker f
  · exact isLocalHom_of_surjective_of_isQuasiregular_ker f hf

end RingHom
