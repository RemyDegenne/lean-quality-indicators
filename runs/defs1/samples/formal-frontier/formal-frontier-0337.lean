@[expose] public section

noncomputable section

namespace GradedRing.Veronese

open DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The `j`th internal component, represented by a single selected summand. -/
def component (n j : ℕ) : AddSubgroup (VeroneseRing 𝒮 n) :=
  AddSubgroup.map (DirectSum.of (fun k : ℕ => 𝒮 (n * k)) j) ⊤

end GradedRing.Veronese
end
end
