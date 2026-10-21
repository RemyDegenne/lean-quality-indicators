namespace OAI

open Erdos970

noncomputable section

namespace Ostmann.Characters.Template.OneSidedPhase

open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate

open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds HigherBiasSourceWord

open DiagonalEstimate

attribute [local instance] Classical.propDecidable

section

variable {d : Decomposition} {E : Finset ℕ} {δ ℓ α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ ℓ k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

theorem sourceSurvivorPrior_mem_of_mass_ne_zero
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k ℓ))→PrimeUpTo s.locations.Q)
    (hp : (sourceSurvivorPrior w j).mass p≠0) (i) : p i∈sourceSurvivorShells w j i := by
  rw [sourceSurvivorPrior_eq_product] at hp
  exact primeProductPrior_mem_of_mass_ne_zero (sourceSurvivorShells w j)
    (sourceSurvivorShells_pos w j) p hp i

end
end Ostmann.Characters.Template.OneSidedPhase
end
end OAI
