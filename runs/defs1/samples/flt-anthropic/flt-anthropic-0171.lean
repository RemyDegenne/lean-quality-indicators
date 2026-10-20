namespace P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd

attribute [-instance] CohCarrier.GammaHLower_finiteIndex

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

namespace OccupancyDvdSol

open CohCarrier IharaLemma

open scoped IsMulCommutative MatrixGroups

open CongruenceSubgroup

section TwoLevels

variable (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
  (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
  (hcomm : ∀ g g' : Gen N S,
      opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 g' = opFamily N ⊤ S 𝒪 g' * opFamily N ⊤ S 𝒪 g)
  (hcomm' : ∀ g g' : Gen (N * q) S,
      opFamily (N * q) ⊤ S 𝒪 g * opFamily (N * q) ⊤ S 𝒪 g' =
        opFamily (N * q) ⊤ S 𝒪 g' * opFamily (N * q) ⊤ S 𝒪 g)
  (θbar : Gen N S → k) (θbar' : Gen (N * q) S → k)

local notation3 "𝕋" => (CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra

local notation3 "𝕋'" => (CohCarrier.hdata (N * q) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra

variable (Sp : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
  (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)
  (hπk : ∀ g : Gen N S, πk (Sp.toCornerRing i₀
    ⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
  (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q),
    θbar' (Gen.T ℓ hℓ hℓS hℓM) = θbar (Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h q))))
  (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓN : ℓ ∣ N), ℓ ≠ q →
    θbar' (Gen.U ℓ hℓ hℓM) = θbar (Gen.U ℓ hℓ hℓN))
  (hθq : θbar' (Gen.U q hq (dvd_mul_left q N)) = 0)
  (hθdia : ∀ d : (ZMod (N * q))ˣ, θbar' (Gen.dia d) = 1)

noncomputable def wL : H1 N ⊤ 𝒪 →ₗ[𝒪] H1 (N * q) ⊤ 𝒪 :=
  (iDegL N (N * q) ⊤ ⊤ q 𝒪 𝒪 hq').comp (heckeTL N ⊤ 𝒪 q)
    - (q : 𝒪) • iDegL N (N * q) ⊤ ⊤ 1 𝒪 𝒪 h1

end TwoLevels
end OccupancyDvdSol
end
end P2MW.S_CohCarrier_exists_idempotentSplitting_algHom_apply_toCornerRing_eq_level_mul_of_prime_of_dvd
