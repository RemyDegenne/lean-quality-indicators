@[expose] public section

noncomputable section

namespace GradedRing.Veronese.CoherentTail

open DirectSum

universe u v w z

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]
  {σ : Type v} {τ : Type z} [SetLike σ R] [AddSubgroupClass σ R]
  [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Coherent identifications of degree zero and all degrees past a positive cutoff.
The products are the products of the original graded rings. -/
structure TailEquiv (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (N : ℕ)
    [GradedRing 𝒜] [GradedRing ℬ] where
  positive : 0 < N
  zero : 𝒜 0 ≃+* ℬ 0
  high : ∀ d, N ≤ d → 𝒜 d ≃+ ℬ d
  coeff : ∀ d (hd : N ≤ d) (a : 𝒜 0) (x : 𝒜 d),
    ((high d hd ⟨(a : R) * x, by
      simpa only [zero_add] using
        (SetLike.GradedMul.mul_mem a.property x.property :
          (a : R) * x ∈ 𝒜 (0 + d))⟩ : ℬ d) : S) =
      (zero a : S) * (high d hd x : S)
  product : ∀ d k (hd : N ≤ d) (hk : N ≤ k) (x : 𝒜 d) (y : 𝒜 k),
    ((high (d + k) (hd.trans (Nat.le_add_right d k))
      ⟨(x : R) * y, SetLike.GradedMul.mul_mem x.property y.property⟩ : ℬ (d + k)) : S) =
      (high d hd x : S) * (high k hk y : S)

end GradedRing.Veronese.CoherentTail
end
end
