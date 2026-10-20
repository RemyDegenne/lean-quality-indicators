@[expose] public section

noncomputable section

namespace GradedRing.Veronese

open DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

def reindex (n : ℕ) : VeroneseRing 𝒮 n →+ ⨁ (i : ℕ), 𝒮 i :=
  DirectSum.toAddMonoid fun j => DirectSum.of (fun i : ℕ => 𝒮 i) (n * j)

end GradedRing.Veronese
end
end
