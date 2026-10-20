namespace P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd

attribute [-instance] CohCarrier.GammaHLower_finiteIndex

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

noncomputable section

namespace LevelRaisingCornerDvdSol

open CohCarrier IharaLemma Polynomial

open scoped IsMulCommutative MatrixGroups

open CongruenceSubgroup

section TwoLevels

variable (N q : ℕ) [NeZero N] [NeZero q] (hq : q.Prime) (hqN : q ∣ N)
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)
  (S : Set ℕ) (hqS : q ∈ S) (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
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
  (Sp' : IharaLemma.IdempotentSplitting
    ↥(CohCarrier.hdata (N * q) ⊤ S 𝒪 k hcomm' θbar').opSubalgebra)
  (i₀' : Fin Sp'.n) (πk' : Sp'.CornerRing i₀' →ₐ[𝒪] k)
  (hπk' : ∀ g : Gen (N * q) S, πk' (Sp'.toCornerRing i₀'
    ⟨(hdata (N * q) ⊤ S 𝒪 k hcomm' θbar').op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
      θbar' g)
  (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ N * q),
    θbar' (Gen.T ℓ hℓ hℓS hℓM) = θbar (Gen.T ℓ hℓ hℓS (fun h => hℓM (Dvd.dvd.mul_right h q))))
  (hθU : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ N * q) (hℓN : ℓ ∣ N), ℓ ≠ q →
    θbar' (Gen.U ℓ hℓ hℓM) = θbar (Gen.U ℓ hℓ hℓN))
  (hθq : θbar' (Gen.U q hq (dvd_mul_left q N)) = 0)

include hqN in

theorem heckeT_wL_eq_zero (v : H1 N ⊤ 𝒪) : heckeT (N * q) ⊤ q 𝒪 (wL N q h1 hq' 𝒪 v) = 0 := by
  rw [wL_apply, map_sub, heckeT_iDeg_q_eq_smul h1 hq' (heckeT N ⊤ q 𝒪 v), heckeT_smul,
    heckeT_iDeg_one_comm_of_dvd h1 hqN v, Nat.cast_smul_eq_nsmul, sub_self]

end TwoLevels
end LevelRaisingCornerDvdSol
end
end P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd
