namespace OAI

noncomputable section

namespace InternalCatalan

theorem manuscriptCase2X6XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((-63243847650671356310893479192004383733 / 625000000000000000000000000000000000000) : ℝ) ((-1011901562410741635015847366981256514619 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-63243847650671356310893479192004383733 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XP8Interval.2 : ℝ) ≤ ((-1011901562410741635015847366981256514619 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XP8_exact_interval.1, manuscriptCase2X6XP8_exact_interval.2.trans hhi⟩

end InternalCatalan
end
end OAI
