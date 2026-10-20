@[expose] public section

noncomputable section

namespace GradedRing.Veronese.CoherentTail

open DirectSum

universe u v w z

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]
  {σ : Type v} {τ : Type z} [SetLike σ R] [AddSubgroupClass σ R]
  [SetLike τ S] [AddSubgroupClass τ S]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

namespace TailEquiv

variable {N : ℕ}

variable (E : TailEquiv 𝒜 ℬ N) (n : ℕ) (hNn : N ≤ n)

theorem piece_mul_symm (i j : ℕ) (x : ℬ (n * i)) (y : ℬ (n * j)) :
    (E.pieceEquiv n hNn (i + j)).symm
      (GradedMonoid.GMul.mul (A := fun k : ℕ => ℬ (n * k)) x y) =
      GradedMonoid.GMul.mul (A := fun k : ℕ => 𝒜 (n * k))
        ((E.pieceEquiv n hNn i).symm x) ((E.pieceEquiv n hNn j).symm y) := by
  apply (E.pieceEquiv n hNn (i + j)).injective
  simpa only [AddEquiv.apply_symm_apply] using
    (E.piece_mul n hNn i j ((E.pieceEquiv n hNn i).symm x)
      ((E.pieceEquiv n hNn j).symm y)).symm

end TailEquiv
end GradedRing.Veronese.CoherentTail
end
end
