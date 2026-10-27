namespace P2MW.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing CohCarrier IharaLemma

open scoped IsMulCommutative

namespace E5Bridge

section theta

variable {M : ℕ} {S : Finset ℕ} {S₀ : Set ℕ}
  (hSS₀ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ℓ ∈ S₀ ↔ ℓ ∈ (↑S : Set ℕ)))
  {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (cfull : CohCarrier.Gen M (↑S : Set ℕ) → 𝒪)

noncomputable def θb : CohCarrier.Gen M S₀ → ResidueField 𝒪
  | .T ℓ hℓ hℓS₀ hℓM => residue 𝒪 (cfull (.T ℓ hℓ (fun h => hℓS₀ ((hSS₀ ℓ hℓ hℓM).2 h)) hℓM))
  | .U q hq hqM => residue 𝒪 (cfull (.U q hq hqM))
  | .dia _ => 1

end theta
end E5Bridge
end P2MW.S_CohCarrier_exists_hdata_corner_of_subfamily_corner_top
