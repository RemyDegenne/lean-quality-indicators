namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

theorem manuscriptNormVCompositionRow9_error :
    |manuscriptNormLogRow barrierV2Tail (barrierV2Tail.getD 9 (0, 0)) - (manuscriptNormVSubstituteRow9 : ℝ)| ≤ (((170276299207 / 200000000000000000000000000000) : ℚ) : ℝ) := by
  have h0 := manuscriptNormV9_0SubstituteRat_composition_error
  have h1 := manuscriptNormV9_1SubstituteRat_composition_error
  have h2 := manuscriptNormV9_2SubstituteRat_composition_error
  have h3 := manuscriptNormV9_3SubstituteRat_composition_error
  have h4 := manuscriptNormV9_4SubstituteRat_composition_error
  have h5 := manuscriptNormV9_5SubstituteRat_composition_error
  have h6 := manuscriptNormV9_6SubstituteRat_composition_error
  have h7 := manuscriptNormV9_7SubstituteRat_composition_error
  have h8 := manuscriptNormV9_8SubstituteRat_composition_error
  have h9 := manuscriptNormV9_9SubstituteRat_composition_error
  have h10 := manuscriptNormV9_10SubstituteRat_composition_error
  have h11 := manuscriptNormV9_11SubstituteRat_composition_error
  have h12 := manuscriptNormV9_12SubstituteRat_composition_error
  push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  change |(manuscriptNormV9_0Term + (manuscriptNormV9_1Term + (manuscriptNormV9_2Term + (manuscriptNormV9_3Term + (manuscriptNormV9_4Term + (manuscriptNormV9_5Term + (manuscriptNormV9_6Term + (manuscriptNormV9_7Term + (manuscriptNormV9_8Term + (manuscriptNormV9_9Term + (manuscriptNormV9_10Term + (manuscriptNormV9_11Term + (manuscriptNormV9_12Term + (0 : ℝ)))))))))))))) - (manuscriptNormVSubstituteRow9 : ℝ)| ≤ _
  unfold manuscriptNormVSubstituteRow9
  push_cast
  apply abs_le.mpr
  constructor
  · linarith only [(abs_le.mp h0).1,
    (abs_le.mp h1).1,
    (abs_le.mp h2).1,
    (abs_le.mp h3).1,
    (abs_le.mp h4).1,
    (abs_le.mp h5).1,
    (abs_le.mp h6).1,
    (abs_le.mp h7).1,
    (abs_le.mp h8).1,
    (abs_le.mp h9).1,
    (abs_le.mp h10).1,
    (abs_le.mp h11).1,
    (abs_le.mp h12).1]
  · linarith only [(abs_le.mp h0).2,
    (abs_le.mp h1).2,
    (abs_le.mp h2).2,
    (abs_le.mp h3).2,
    (abs_le.mp h4).2,
    (abs_le.mp h5).2,
    (abs_le.mp h6).2,
    (abs_le.mp h7).2,
    (abs_le.mp h8).2,
    (abs_le.mp h9).2,
    (abs_le.mp h10).2,
    (abs_le.mp h11).2,
    (abs_le.mp h12).2]

end InternalCatalan
end
end
end OAI
