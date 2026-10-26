/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# A projective radical criterion

For a positive-degree homogeneous element, vanishing at every relevant
homogeneous prime over a homogeneous ideal is equivalent to membership in the
ordinary radical of that ideal.
-/

@[expose] public section

namespace ProjectiveSpectrum

universe u v

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A positive-degree homogeneous element vanishes at every relevant
homogeneous prime containing `I` if and only if it belongs to the ordinary
radical of `I`.

No containment of `I` in the irrelevant ideal is needed. -/
theorem mem_vanishingIdeal_zeroLocus_iff_mem_radical
    (I : HomogeneousIdeal 𝒜) {f : A} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    f ∈ vanishingIdeal (zeroLocus 𝒜 I) ↔ f ∈ I.toIdeal.radical := by
  constructor
  · intro h
    by_contra hfrad
    have hdisj : Disjoint (I.toIdeal : Set A) (Submonoid.powers f) := by
      rw [Set.disjoint_right]
      intro x hxpow hxI
      change x ∈ Submonoid.powers f at hxpow
      rw [Submonoid.mem_powers_iff] at hxpow
      obtain ⟨k, rfl⟩ := hxpow
      exact hfrad ⟨k, hxI⟩
    obtain ⟨p, hp, hIp, hpdisj⟩ := I.toIdeal.exists_le_prime_disjoint (.powers f) hdisj
    let q : HomogeneousIdeal 𝒜 := p.homogeneousCore 𝒜
    have hIq : I ≤ q :=
      I.isHomogeneous.toIdeal_homogeneousCore_eq_self.symm.trans_le
        (Ideal.homogeneousCore_mono 𝒜 hIp)
    have hfq : f ∉ q := by
      intro hfq
      exact Set.disjoint_right.mp hpdisj (Submonoid.mem_powers f)
        (Ideal.toIdeal_homogeneousCore_le 𝒜 p hfq)
    have hfirr : f ∈ HomogeneousIdeal.irrelevant 𝒜 :=
      HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hf
    let x : ProjectiveSpectrum 𝒜 :=
      ⟨q, hp.homogeneousCore, fun hrel => hfq (hrel hfirr)⟩
    exact hfq ((mem_vanishingIdeal _ _).mp h x ((mem_zeroLocus _ _ _).mpr hIq))
  · intro h
    rw [mem_vanishingIdeal]
    intro x hx
    obtain ⟨k, hk⟩ := h
    exact x.isPrime.mem_of_pow_mem k (((mem_zeroLocus _ _ _).mp hx) hk)

end ProjectiveSpectrum
