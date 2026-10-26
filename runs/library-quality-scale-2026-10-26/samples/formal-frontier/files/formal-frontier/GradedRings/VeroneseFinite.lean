/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GradedRings.Veronese
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Finiteness of positive Veronese inclusions

If a naturally graded commutative ring is of finite type over its whole degree-zero
ring, its canonical map from any positive selected-component Veronese ring is finite.
-/

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false

noncomputable section

namespace GradedRing.Veronese

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The original graded ring is a finite module over its positive Veronese ring
via the canonical inclusion, assuming finite type over the entire degree-zero ring. -/
theorem inclusion_finite (n : ℕ) (hn : 0 < n) [Algebra.FiniteType (𝒮 0) S] :
    (inclusion 𝒮 n).Finite := by
  classical
  letI : Algebra (VeroneseRing 𝒮 n) S := (inclusion 𝒮 n).toAlgebra
  obtain ⟨generators, hgen, hhom⟩ :=
    GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous 𝒮
  have hintegral : ∀ x ∈ (generators : Set S), IsIntegral (VeroneseRing 𝒮 n) x := by
    intro x hx
    obtain ⟨degree, hdegree⟩ := hhom x (Finset.mem_coe.mp hx)
    have hpower : x ^ n ∈ 𝒮 (n * degree) := by
      simpa [nsmul_eq_mul] using SetLike.pow_mem_graded n hdegree
    obtain ⟨preimage, _, heq⟩ := exists_component 𝒮 n degree ⟨x ^ n, hpower⟩
    apply IsIntegral.of_pow hn
    have hmap : x ^ n = algebraMap (VeroneseRing 𝒮 n) S preimage := by
      change x ^ n = inclusion 𝒮 n preimage
      exact heq.symm
    rw [hmap]
    exact isIntegral_algebraMap
  have hold : ∀ x : S, x ∈ Algebra.adjoin (𝒮 0) (generators : Set S) →
      x ∈ Algebra.adjoin (VeroneseRing 𝒮 n) (generators : Set S) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap a =>
      have hzero : (a : S) ∈ 𝒮 (n * 0) := by simpa only [mul_zero] using a.property
      obtain ⟨preimage, _, heq⟩ := exists_component 𝒮 n 0 ⟨(a : S), hzero⟩
      have hmap : algebraMap (𝒮 0) S a =
          algebraMap (VeroneseRing 𝒮 n) S preimage := by
        change (a : S) = inclusion 𝒮 n preimage
        exact heq.symm
      rw [hmap]
      exact Subalgebra.algebraMap_mem _ preimage
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hnew : Algebra.adjoin (VeroneseRing 𝒮 n) (generators : Set S) = ⊤ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      apply hold
      rw [hgen]
      trivial
  have hfg : (⊤ : Submodule (VeroneseRing 𝒮 n) S).FG := by
    simpa only [hnew, Algebra.top_toSubmodule] using
      (fg_adjoin_of_finite (R := VeroneseRing 𝒮 n) generators.finite_toSet hintegral)
  exact Module.Finite.of_fg_top hfg

end GradedRing.Veronese
