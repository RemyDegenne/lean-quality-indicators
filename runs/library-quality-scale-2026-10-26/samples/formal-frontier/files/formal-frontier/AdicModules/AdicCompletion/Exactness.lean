/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The Cauchy-sequence argument follows the Mathlib formalization:
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of that formalization: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Exactness of completion under range cofinality

Adic completion preserves middle exactness when the topology induced on the range
of the first map is cofinal with its intrinsic adic topology. Neither injectivity
of the first map nor finiteness or Noetherian hypotheses are required.

## Implementation notes

The proof uses the existing Cauchy-sequence and completion maps. At each step,
cofinality allows a change of a chosen lift by an element in the required ideal
power. The change need not equal the difference of the original lifts, so the
first map need not be injective. No intrinsic adic completeness of a completion
is assumed.

## References

The construction follows the Cauchy-sequence proof of `AdicCompletion.map_exact`
by Judith Ludwig and Christian Merten in
`Mathlib.RingTheory.AdicCompletion.Exactness`. Pointwise range cofinality replaces
its Artin–Rees bound, and chosen small changes replace its use of injectivity.
-/

@[expose] public section

universe uR uP uN uM

namespace AdicCompletion

open LinearMap

variable {R : Type uR} [CommRing R] {I : Ideal R}
variable {P : Type uP} [AddCommGroup P] [Module R P]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {f : P →ₗ[R] N} {g : N →ₗ[R] M}

private theorem exists_cofinal_indices
    (hcofinal : ∀ k : ℕ, ∃ l : ℕ,
      f.range ⊓ (I ^ l • ⊤ : Submodule R N) ≤ I ^ k • f.range) :
    ∃ e : ℕ → ℕ, (∀ n, n ≤ e n) ∧ (∀ n, e n ≤ e (n + 1)) ∧
      ∀ n, f.range ⊓ (I ^ e n • ⊤ : Submodule R N) ≤ I ^ n • f.range := by
  classical
  choose l hl using hcofinal
  let e : ℕ → ℕ := Nat.rec (l 0) (fun n m ↦ max (m + 1) (l (n + 1)))
  have hl_e (n : ℕ) : l n ≤ e n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have he_step (n : ℕ) : e n ≤ e (n + 1) :=
    (Nat.le_succ (e n)).trans (le_max_left _ _)
  have he_bound (n : ℕ) : n ≤ e n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact (Nat.succ_le_succ ih).trans (le_max_left _ _)
  refine ⟨e, he_bound, he_step, fun n z hz ↦ ?_⟩
  exact hl n ⟨hz.1,
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (hl_e n))) hz.2⟩

private theorem exists_exact_approximation
    (hExact : Function.Exact f g) (hg : Function.Surjective g)
    (x : AdicCauchySequence I N)
    (hker : ∀ n : ℕ, g (x n) ∈ (I ^ n • ⊤ : Submodule R M)) (n : ℕ) :
    ∃ y : P, f y - x n ∈ (I ^ n • ⊤ : Submodule R N) := by
  have hmem : g (x n) ∈ Submodule.map g (I ^ n • ⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, range_eq_top.mpr hg]
    exact hker n
  obtain ⟨d, hdmem, hd⟩ := hmem
  obtain ⟨y, hy⟩ := (hExact (x n - d)).mp (by simp [hd])
  refine ⟨y, ?_⟩
  simpa [hy] using (Submodule.neg_mem _ hdmem)

/-- A small change of a lift, not necessarily the difference of two chosen lifts. -/
private noncomputable def exactLiftDelta
    (e : ℕ → ℕ) (he : ∀ n, e n ≤ e (n + 1))
    (hcofinal : ∀ n, f.range ⊓ (I ^ e n • ⊤ : Submodule R N) ≤ I ^ n • f.range)
    (x : AdicCauchySequence I N) {n : ℕ} {y p : P}
    (hy : f y - x (e (n + 1)) ∈ (I ^ e (n + 1) • ⊤ : Submodule R N))
    (hp : f p - x (e n) ∈ (I ^ e n • ⊤ : Submodule R N)) :
    {δ : (I ^ n • ⊤ : Submodule R P) |
      f (p + δ) - x (e (n + 1)) ∈ (I ^ e (n + 1) • ⊤ : Submodule R N)} := by
  have hx : x (e (n + 1)) - x (e n) ∈ (I ^ e n • ⊤ : Submodule R N) := by
    rw [← Submodule.Quotient.eq]
    exact AdicCauchySequence.mk_eq_mk (he n) x
  have hy' : f y - x (e (n + 1)) ∈ (I ^ e n • ⊤ : Submodule R N) :=
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (he n))) hy
  have hdiff : f (y - p) ∈ (I ^ e n • ⊤ : Submodule R N) := by
    rw [map_sub]
    convert Submodule.sub_mem _ (Submodule.add_mem _ hy' hx) hp using 1 <;> abel
  have hmem : f (y - p) ∈ Submodule.map f (I ^ n • ⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact hcofinal n ⟨⟨y - p, rfl⟩, hdiff⟩
  refine ⟨⟨hmem.choose, hmem.choose_spec.1⟩, ?_⟩
  have hδ : f hmem.choose = f (y - p) := hmem.choose_spec.2
  have hfy : f (p + hmem.choose) = f y := by
    rw [map_add, hδ, map_sub]
    abel
  change f (p + hmem.choose) - x (e (n + 1)) ∈
    (I ^ e (n + 1) • ⊤ : Submodule R N)
  simpa only [hfy] using hy

/-- Successive approximations whose changes have the prescribed intrinsic precision. -/
private noncomputable def exactLift
    (hExact : Function.Exact f g) (hg : Function.Surjective g)
    (e : ℕ → ℕ) (he : ∀ n, e n ≤ e (n + 1))
    (hcofinal : ∀ n, f.range ⊓ (I ^ e n • ⊤ : Submodule R N) ≤ I ^ n • f.range)
    (x : AdicCauchySequence I N)
    (hker : ∀ n : ℕ, g (x n) ∈ (I ^ n • ⊤ : Submodule R M)) :
    (n : ℕ) → {p : P | f p - x (e n) ∈ (I ^ e n • ⊤ : Submodule R N)}
  | .zero =>
      let h := exists_exact_approximation hExact hg x hker (e 0)
      ⟨h.choose, h.choose_spec⟩
  | .succ n =>
      let h := exists_exact_approximation hExact hg x hker (e (n + 1))
      let p := exactLift hExact hg e he hcofinal x hker n
      let δ := exactLiftDelta e he hcofinal x h.choose_spec p.property
      ⟨(p : P) + (δ.val : P), δ.property⟩

/-- Adic completion preserves middle exactness if the induced adic filtration on
`f.range` is cofinal with the intrinsic filtration `I ^ k • f.range`.

This generalizes Mathlib's `AdicCompletion.map_exact`: range cofinality replaces
its Noetherian and finiteness assumptions, and the first map need not be injective.
Cofinality ensures that successive lifts can be corrected by intrinsically small
elements; it is not an intrinsic completeness assumption on the completed modules. -/
theorem map_exact_of_range_cofinal
    (hExact : Function.Exact f g) (hg : Function.Surjective g)
    (hcofinal : ∀ k : ℕ, ∃ l : ℕ,
      f.range ⊓ (I ^ l • ⊤ : Submodule R N) ≤ I ^ k • f.range) :
    Function.Exact (map I f) (map I g) := by
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ (fun z ↦ ?_)
  · rw [map_comp, hExact.linearMap_comp_eq_zero, AdicCompletion.map_zero]
  · apply AdicCompletion.induction_on I N z (fun b ↦ ?_)
    intro hz
    obtain ⟨e, he_bound, he_step, he_cofinal⟩ := exists_cofinal_indices hcofinal
    have hb (n : ℕ) : g (b n) ∈ (I ^ n • ⊤ : Submodule R M) := by
      simpa using congrArg (fun z ↦ z.val n) hz
    let a := exactLift hExact hg e he_step he_cofinal b hb
    refine ⟨AdicCompletion.mk I P (AdicCauchySequence.mk I P (fun n ↦ (a n : P)) ?_), ?_⟩
    · intro n
      apply SModEq.symm
      simp [a, exactLift, SModEq]
    · ext n
      suffices h : Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f (a n)) =
          Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (b (e n)) by
        simp [h, AdicCauchySequence.mk_eq_mk (he_bound n)]
      rw [Submodule.Quotient.eq]
      exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (he_bound n))) (a n).property

/-- Artin–Rees supplies range cofinality for a finite middle module over a Noetherian ring. -/
private theorem map_exact_of_finite_of_isNoetherian
    [IsNoetherianRing R] [Module.Finite R N]
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (map I f) (map I g) := by
  apply map_exact_of_range_cofinal hExact hg
  intro k
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I f.range
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hc (k + c) (Nat.le_add_left c k), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

end AdicCompletion
