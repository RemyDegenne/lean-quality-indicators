public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open SCFourCover

theorem ggNbrLSide35At_twA
    (rank n : ℕ) : GGNbrLSide35At ⟨.twA, rank, n⟩ := by
  intro hrank L _ _ hL
  refine ggNbrLSide35At_of_torusLift (fun hlab hs => ?_) L hL
  have h3 : 3 ∣ 2 ^ n + 1 := by
    simp [LargeEvenSplit, LargeEvenUntwisted] at hs
    rcases hs with h | rfl
    · exact h
    · norm_num
  unfold GGNbrLSideLargeRank at hrank
  simp only [ggNbrLSideRank] at hrank
  rcases hrank with ⟨he, -⟩ | ⟨-, h12⟩
  · exact absurd he (ggNbrLSide_not_even_of_dvd_pow_add h3)
  · exact largeEvenLabelAll_torusLift_twA_threeFive hlab rfl h3 (by show 7 ≤ rank + 1; omega)

end CFSG.StandardType
end
