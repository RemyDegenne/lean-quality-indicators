/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Support

/-!
# Pseudo-null modules

Pseudo-nullity means vanishing at primes of height at most one. This predicate
uses support over an arbitrary commutative ring; no finite-generation or
Noetherian hypothesis is imposed. The public API gives localization, submodule,
quotient and short-exact-sequence characterizations.
-/

public section

set_option warningAsError true

namespace Module

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- A module is pseudo-null when it vanishes after localization at every prime
of height at most one. Finiteness hypotheses belong on structure theorems, not
on this predicate. -/
@[expose] def IsPseudoNull : Prop :=
  ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 → p ∉ Module.support R M

/-- Pseudo-nullity restated directly in terms of localized modules. -/
theorem isPseudoNull_iff_localizedModule_subsingleton :
    IsPseudoNull R M ↔
      ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  simp only [IsPseudoNull, Module.notMem_support_iff]

/-- Every subsingleton module is pseudo-null. -/
theorem IsPseudoNull.of_subsingleton [Subsingleton M] : IsPseudoNull R M := by
  intro p _
  rw [Module.notMem_support_iff]
  infer_instance

variable {R M}
variable {N P : Type*} [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- A submodule of a pseudo-null module is pseudo-null, expressed for an
arbitrary injective linear map. -/
theorem IsPseudoNull.of_injective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hN : IsPseudoNull R N) : IsPseudoNull R M := by
  intro p hp hMp
  exact hN p hp (Module.support_subset_of_injective f hf hMp)

/-- A quotient of a pseudo-null module is pseudo-null, expressed for an
arbitrary surjective linear map. -/
theorem IsPseudoNull.of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : IsPseudoNull R M) : IsPseudoNull R N := by
  intro p hp hNp
  exact hM p hp (Module.support_subset_of_surjective f hf hNp)

/-- Pseudo-null modules are closed under extensions. -/
theorem IsPseudoNull.of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hM : IsPseudoNull R M)
    (hP : IsPseudoNull R P) : IsPseudoNull R N := by
  intro p hp hNp
  rw [Module.support_of_exact h hf hg] at hNp
  exact hNp.elim (hM p hp) (hP p hp)

/-- In a short exact sequence, the middle module is pseudo-null exactly when
both outer modules are pseudo-null. -/
theorem isPseudoNull_iff_of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    IsPseudoNull R N ↔ IsPseudoNull R M ∧ IsPseudoNull R P := by
  refine ⟨fun hN => ⟨hN.of_injective f hf, hN.of_surjective g hg⟩, ?_⟩
  rintro ⟨hM, hP⟩
  exact IsPseudoNull.of_exact f g h hf hg hM hP

/-- A module is pseudo-null exactly when a submodule and the corresponding
quotient are both pseudo-null. -/
theorem isPseudoNull_iff_submodule_quotient (Q : Submodule R M) :
    IsPseudoNull R M ↔ IsPseudoNull R Q ∧ IsPseudoNull R (M ⧸ Q) :=
  isPseudoNull_iff_of_exact Q.subtype Q.mkQ
    (LinearMap.exact_subtype_mkQ Q) Q.subtype_injective Q.mkQ_surjective

end Module

namespace LinearEquiv

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Pseudo-nullity is invariant under a linear equivalence. -/
theorem isPseudoNull_iff (e : M ≃ₗ[R] N) :
    Module.IsPseudoNull R M ↔ Module.IsPseudoNull R N :=
  ⟨Module.IsPseudoNull.of_surjective e.toLinearMap e.surjective,
    Module.IsPseudoNull.of_surjective e.symm.toLinearMap e.symm.surjective⟩

end LinearEquiv
