/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Modules annihilated by a power of an ideal

This file develops the elementary API for a module on which one power of a
fixed ideal acts by zero. The exponent is uniform over the whole module. This
is stronger than asking separately for every element to be killed by some
ideal power. Tensoring with any module preserves the same annihilating set
and hence the same ideal power.

A product is annihilated by an ideal power exactly when its factors share one
exponent. For finitely many factors, separate bounds give a common bound. For an
infinite family, pointwise bounds need not be uniform.

## References

Mathlib's `Module.IsTorsionBySet`, annihilator and ideal-primary-component APIs
supply the torsion interfaces used by the finite-module uniform-exponent bridge.
The product API uses Mathlib's `Module.annihilator_pi` and
`Module.isTorsionBySet_iff_subset_annihilator`; the finite bound is supplied by
`Finite.exists_le` from the finite-order development of Peter Nelson and Yaël Dillies.
The original bounded-torsion implementation and its project-source adaptation
are credited separately in `docs/CREDITS.md`.
-/

@[expose] public section

universe u v w

namespace Module

section AddCommMonoid

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `IsKilledByIdealPower R M I` means that one power of `I` annihilates the
whole module `M`. -/
def IsKilledByIdealPower (I : Ideal R) : Prop :=
  ∃ n : ℕ, Module.IsTorsionBySet R M (↑(I ^ n) : Set R)

/-- A module is killed by a power of an ideal exactly when some ideal power is
contained in its annihilator. -/
theorem isKilledByIdealPower_iff_exists_pow_le_annihilator (I : Ideal R) :
    IsKilledByIdealPower R M I ↔ ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  simp only [IsKilledByIdealPower, Module.isTorsionBySet_iff_subset_annihilator]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn⟩

/-- Once a power of an ideal annihilates a module, every larger power does too. -/
theorem isTorsionBySet_ideal_pow_of_le (I : Ideal R) {n m : ℕ} (hnm : n ≤ m)
    (h : Module.IsTorsionBySet R M (↑(I ^ n) : Set R)) :
    Module.IsTorsionBySet R M (↑(I ^ m) : Set R) :=
  Module.isTorsionBySet_of_subset (Ideal.pow_le_pow_right hnm) h

variable {R M}

/-- If a power of `I` annihilates a module, then a power of every smaller ideal
does as well. -/
theorem IsKilledByIdealPower.of_le {I J : Ideal R} (hI : IsKilledByIdealPower R M I)
    (hJI : J ≤ I) : IsKilledByIdealPower R M J := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, Module.isTorsionBySet_of_subset (R := R) (M := M)
    (Ideal.pow_right_mono hJI n) hn⟩

/-- Every submodule of a module annihilated by an ideal power is annihilated by
the same ideal power. -/
theorem IsKilledByIdealPower.submodule {I : Ideal R} (h : IsKilledByIdealPower R M I)
    (N : Submodule R M) : IsKilledByIdealPower R N I := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun x a ↦ Subtype.ext ?_⟩
  exact @hn x.1 a

/-- Surjective linear images preserve annihilation by an ideal power. -/
theorem IsKilledByIdealPower.of_surjective {N : Type w} [AddCommMonoid N] [Module R N]
    {I : Ideal R} (hM : IsKilledByIdealPower R M I) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : IsKilledByIdealPower R N I := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, ?_⟩
  intro y a
  obtain ⟨x, rfl⟩ := hf y
  simpa only [map_smul, map_zero] using congrArg f (@hn x a)

section TensorProduct

open scoped TensorProduct

variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Any set of scalars annihilating the left factor annihilates the tensor product. -/
theorem IsTorsionBySet.tensorProduct_left {s : Set R} (hM : IsTorsionBySet R M s) :
    IsTorsionBySet R (M ⊗[R] N) s := by
  intro x a
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
      rw [TensorProduct.smul_tmul', @hM m a, TensorProduct.zero_tmul]
  | add x y hx hy =>
      rw [smul_add, hx, hy, add_zero]

/-- Any set of scalars annihilating the right factor annihilates the tensor product. -/
theorem IsTorsionBySet.tensorProduct_right {s : Set R} (hN : IsTorsionBySet R N s) :
    IsTorsionBySet R (M ⊗[R] N) s := by
  have h := hN.tensorProduct_left (N := M)
  intro x a
  apply (TensorProduct.comm R M N).injective
  simpa only [map_smul, map_zero] using @h ((TensorProduct.comm R M N) x) a

/-- If an ideal power annihilates the left factor, that same power annihilates the tensor
product. -/
theorem IsKilledByIdealPower.tensorProduct_left {I : Ideal R}
    (hM : IsKilledByIdealPower R M I) : IsKilledByIdealPower R (M ⊗[R] N) I := by
  obtain ⟨n, hn⟩ := hM
  exact ⟨n, hn.tensorProduct_left⟩

/-- If an ideal power annihilates the right factor, that same power annihilates the tensor
product. -/
theorem IsKilledByIdealPower.tensorProduct_right {I : Ideal R}
    (hN : IsKilledByIdealPower R N I) : IsKilledByIdealPower R (M ⊗[R] N) I := by
  obtain ⟨n, hn⟩ := hN
  exact ⟨n, hn.tensorProduct_right⟩

end TensorProduct

end AddCommMonoid

section Pi

variable (R : Type u) {ι : Type w} (M : ι → Type v) [CommSemiring R]
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- A product is killed by a power of `I` exactly when one exponent kills every
factor. For an infinite index type, separate factor bounds need not be uniform. -/
theorem isKilledByIdealPower_pi_iff (I : Ideal R) :
    IsKilledByIdealPower R (Π i, M i) I ↔
      ∃ n : ℕ, ∀ i, IsTorsionBySet R (M i) (↑(I ^ n) : Set R) := by
  rw [isKilledByIdealPower_iff_exists_pow_le_annihilator, Module.annihilator_pi]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun i ↦ ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator]
    exact (le_iInf_iff.mp hn) i
  · rintro ⟨n, hn⟩
    refine ⟨n, le_iInf fun i ↦ ?_⟩
    exact (Module.isTorsionBySet_iff_subset_annihilator R (M i)).mp (hn i)

/-- A finite product is killed by an ideal power exactly when each factor is.
`Finite.exists_le` gives a common bound, including for the empty index type. -/
@[simp]
theorem isKilledByIdealPower_pi_iff_of_finite [_root_.Finite ι] (I : Ideal R) :
    IsKilledByIdealPower R (Π i, M i) I ↔ ∀ i, IsKilledByIdealPower R (M i) I := by
  rw [isKilledByIdealPower_pi_iff R M I]
  constructor
  · rintro ⟨n, hn⟩ i
    exact ⟨n, hn i⟩
  · intro h
    classical
    choose n hn using h
    obtain ⟨m, hm⟩ := Finite.exists_le n
    exact ⟨m, fun i ↦ isTorsionBySet_ideal_pow_of_le R (M i) I (hm i) (hn i)⟩

end Pi

section Finite

variable (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M]

/-- On a finite module, elementwise annihilation by ideal powers is equivalent
to annihilation of the whole module by one uniform ideal power. -/
theorem isKilledByIdealPower_iff_primaryComponent_eq_top [Module.Finite R M]
    (I : Ideal R) :
    IsKilledByIdealPower R M I ↔ Ideal.primaryComponent M I = ⊤ := by
  constructor
  · rintro ⟨n, hn⟩
    rw [eq_top_iff]
    intro x _
    rw [Ideal.primaryComponent_mem]
    exact ⟨n, (Module.isTorsionBySet_iff_torsionBySet_eq_top _).mp hn ▸ trivial⟩
  · intro h
    rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
    have hmem : ∀ x : M, ∃ n, x ∈ Submodule.torsionBySet R M ↑(I ^ n) := by
      intro x
      rw [← Ideal.primaryComponent_mem, h]
      trivial
    choose g hg using hmem
    refine ⟨Finset.sup S g, ?_⟩
    rw [Module.isTorsionBySet_iff_torsionBySet_eq_top]
    apply top_unique
    rw [← hS]
    refine Submodule.span_le.mpr fun x hx ↦ ?_
    exact Submodule.torsionBySet_le_torsionBySet_pow _ _ (Finset.le_sup hx) I (hg x)

end Finite

section AddCommGroup

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

variable {R M}

/-- Quotients of a module annihilated by an ideal power are annihilated by the
same ideal power. -/
theorem IsKilledByIdealPower.quotient {I : Ideal R} (h : IsKilledByIdealPower R M I)
    (N : Submodule R M) : IsKilledByIdealPower R (M ⧸ N) I := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  intro y a
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  simpa only [map_smul, map_zero] using congrArg N.mkQ (@hn x a)

/-- If `I ^ n` annihilates a submodule and `I ^ m` annihilates the quotient,
then `I ^ (n + m)` annihilates the whole module. -/
theorem isTorsionBySet_ideal_pow_extension (I : Ideal R) (N : Submodule R M) {n m : ℕ}
    (hN : Module.IsTorsionBySet R N (↑(I ^ n) : Set R))
    (hQ : Module.IsTorsionBySet R (M ⧸ N) (↑(I ^ m) : Set R)) :
    Module.IsTorsionBySet R M (↑(I ^ (n + m)) : Set R) := by
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hN hQ ⊢
  change I ^ n ≤ Module.annihilator R N at hN
  change I ^ m ≤ Module.annihilator R (M ⧸ N) at hQ
  change I ^ (n + m) ≤ Module.annihilator R M
  rw [pow_add, Ideal.mul_le]
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  have hbx : b • x ∈ N := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa only [Submodule.Quotient.mk_smul] using
      (Module.mem_annihilator.mp (hQ hb) (Submodule.Quotient.mk x))
  rw [mul_smul]
  exact Subtype.ext_iff.mp (Module.mem_annihilator.mp (hN ha) ⟨b • x, hbx⟩)

/-- An extension of modules annihilated by powers `I ^ n` and `I ^ m` is
annihilated by `I ^ (n + m)`. -/
theorem IsKilledByIdealPower.extension (I : Ideal R) (N : Submodule R M)
    (hN : IsKilledByIdealPower R N I) (hQ : IsKilledByIdealPower R (M ⧸ N) I) :
    IsKilledByIdealPower R M I := by
  obtain ⟨n, hn⟩ := hN
  obtain ⟨m, hm⟩ := hQ
  exact ⟨n + m, isTorsionBySet_ideal_pow_extension I N hn hm⟩

end AddCommGroup

end Module

@[expose] public section

open Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M] [Module R M]
  [Module.Finite R M]

/-- Every submodule of a finite module equal to its ideal-primary component is
annihilated by one ideal power. Uniformity is obtained on the ambient finite module first;
the submodule itself need not be assumed finite. This uses
`Module.isKilledByIdealPower_iff_primaryComponent_eq_top` and
`Module.IsKilledByIdealPower.submodule`. -/
theorem Module.isKilledByIdealPower_submodule_of_primaryComponent_eq_top
    (I : Ideal R) (h : Ideal.primaryComponent M I = ⊤) (N : Submodule R M) :
    IsKilledByIdealPower R N I :=
  (Module.isKilledByIdealPower_iff_primaryComponent_eq_top R M I).mpr h |>.submodule N

end
