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

def pieceHomSymm (j : ℕ) : ℬ (n * j) →+ VeroneseRing 𝒜 n :=
  (DirectSum.of (fun k : ℕ => 𝒜 (n * k)) j).comp
    (E.pieceEquiv n hNn j).symm.toAddMonoidHom

end TailEquiv
end GradedRing.Veronese.CoherentTail
end
end
