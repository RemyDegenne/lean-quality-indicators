namespace P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime

attribute [-instance] CohCarrier.GammaHLower_finiteIndex

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

namespace LevelRaisingCornerSol

open CohCarrier IharaLemma

open scoped IsMulCommutative MatrixGroups

open CongruenceSubgroup

section Hecke

variable (M : ℕ) [NeZero M] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen M S,
      opFamily M ⊤ S 𝒪 g * opFamily M ⊤ S 𝒪 g' = opFamily M ⊤ S 𝒪 g' * opFamily M ⊤ S 𝒪 g)
  (θbar : Gen M S → k)

local notation3 "𝕋" => (CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata M ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n)

variable (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)

theorem toCornerRing_one_sub_e : Sp.toCornerRing i₀ (1 - Sp.e i₀) = 0 := by
  apply Subtype.ext
  rw [IdempotentSplitting.coe_toCornerRing]
  show Sp.e i₀ * (1 - Sp.e i₀) * Sp.e i₀ = 0
  linear_combination (-Sp.e i₀) * (Sp.idem i₀).eq

end Hecke
end LevelRaisingCornerSol
end
end P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime
