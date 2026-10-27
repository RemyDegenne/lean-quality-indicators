public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Subgroup

open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem dichotomy_of_solvable [Finite G] {L : Subgroup G}
    (hL : IsShort2 L) (hs : Group.IsSolvable L) {K : Subgroup G} (hKL : K ≤ L)
    (hKn : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hK2 : ∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n = 1) :
    K = ⊥ ∨ K = blockQ L := by
  have hUQ : blockU L = blockQ L := blockU_eq_blockQ_of_solvable hL hs
  have hZ : blockZ L = ⊥ := blockZ_eq_bot_of_solvable hL hs
  have hKQ : K ≤ blockQ L := le_pCoreOf_two_of_normal hKL hK2 hKn
  have hKU : K ≤ blockU L := by rw [hUQ]; exact hKQ
  have hnorm : L ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hKn l hl h hh
    · intro hh
      have h1 := hKn l⁻¹ (L.inv_mem hl) _ hh
      have e : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
      rw [e] at h1
      exact h1
  have hW := hL.2.2.2.2.2 K (by rw [hZ]; exact bot_le) hKU hnorm
  rw [hZ, hUQ] at hW
  exact hW

end CFSG.HardMathSupport.Cooperstein.Proving
end
