public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem sec6Setting_exists {X : Type} [Group X] [Finite X] (hc : SolCEx X) (hA : ¬ HypA X)
    {n : ℕ} (hn : IsMaxAhatDeg X n) (hE : Sec6Entry X n)
    (hcen : ∀ t, IsSec6Choice X n t →
      ∃ t', IsSec6Choice X n t' ∧ (K0 X n (cen t') ≠ ⊥ → t' ∈ K0 X n (cen t'))) :
    ∃ t, Sec6Setting X n t := by
  obtain ⟨hdeg, hM⟩ := hE.exists_mcomp
  obtain ⟨t₀, ht₀⟩ := sec6Choice_exists hM
  obtain ⟨t, ht, hcent⟩ := hcen t₀ ht₀
  exact ⟨t, ⟨hc, hA, hn, hdeg, ht, hcent⟩⟩

end CFSG.OddStandard.Solomon75
end
