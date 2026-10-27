public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace TwelveSix

theorem calNIn_eq_inf (D : Data G) {H₀ L : Subgroup G} (hH₀ : ¬ H₀ ≤ D.M) (hT : D.T ≤ H₀)
    (hcalN : calNIn H₀ D.T = {L}) (hL : L ≤ H₀ ⊓ D.M) : calNIn H₀ D.T = {H₀ ⊓ D.M} := by
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).1
  have hlt : H₀ ⊓ D.M < H₀ := lt_of_le_of_ne inf_le_left fun h => hH₀ (inf_eq_left.1 h)
  obtain ⟨X, hX, hle⟩ := exists_mem_calNIn_of_lt (le_inf hT hTM) hlt
  rw [hcalN, Set.mem_singleton_iff] at hX
  subst hX
  rw [hcalN, le_antisymm hL hle]

end TwelveSix
end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
