/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original formalization: Atlas. Module-interface updates: Prism.
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Class groups of Dedekind-domain localizations

This file proves that extension of ideal classes from a Dedekind domain to a
Dedekind localization is surjective. Consequently, if one class generates the
source class group and becomes trivial after localization, then the target is
a principal ideal domain and hence a unique factorization domain.

No injectivity or finiteness of either class group is assumed.
-/

public section

open scoped nonZeroDivisors

universe u v

namespace ClassGroup

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

/-- Extension of ideal classes to a Dedekind localization is surjective. -/
theorem extendedHom_surjective_of_isLocalization
    (M : Submonoid A) [IsLocalization M B] :
    Function.Surjective (ClassGroup.extendedHom A B) := by
  intro c
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  let I : Ideal A := J.1.under A
  have hI : I ≠ ⊥ := by
    intro hI
    have hJ : J.1 = ⊥ := by
      rw [← IsLocalization.map_under M B J.1,
        show J.1.under A = ⊥ from by simpa [I] using hI]
      exact Ideal.map_bot
    exact (mem_nonZeroDivisors_iff_ne_zero.mp J.2) hJ
  let I₀ : (Ideal A)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  refine ⟨ClassGroup.mk0 I₀, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  congr 1
  exact Subtype.ext (IsLocalization.map_under M B J.1)

/-- A Dedekind localization is a PID if a generator of the source class group
becomes trivial. The hypothesis `hgen` says that every class is an integral
power of `g`. -/
theorem isPrincipalIdealRing_of_generator_of_isLocalization
    (M : Submonoid A) [IsLocalization M B]
    (g : ClassGroup A) (hgen : ∀ x : ClassGroup A, x ∈ Subgroup.zpowers g)
    (hkill : ClassGroup.extendedHom A B g = 1) : IsPrincipalIdealRing B := by
  have htrivial : ∀ x : ClassGroup A, ClassGroup.extendedHom A B x = 1 := by
    intro x
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
    rw [map_zpow, hkill, one_zpow]
  have htarget : ∀ y : ClassGroup B, y = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := extendedHom_surjective_of_isLocalization M y
    exact htrivial x
  refine ⟨fun I ↦ ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]
    exact bot_isPrincipal
  · exact (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI)).mp
      (htarget (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩))

/-- A Dedekind localization is a UFD if a generator of the source class group
becomes trivial. -/
theorem uniqueFactorizationMonoid_of_generator_of_isLocalization
    (M : Submonoid A) [IsLocalization M B]
    (g : ClassGroup A) (hgen : ∀ x : ClassGroup A, x ∈ Subgroup.zpowers g)
    (hkill : ClassGroup.extendedHom A B g = 1) : UniqueFactorizationMonoid B := by
  let _ : IsPrincipalIdealRing B :=
    isPrincipalIdealRing_of_generator_of_isLocalization M g hgen hkill
  infer_instance

end ClassGroup
