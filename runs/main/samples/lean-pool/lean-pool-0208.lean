@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

theorem exists_nonnegative_score_of_matched_endpoint_zero
    (configuration : SixPointConfiguration) (h : configuration.IsAdmissibleAt barS)
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    (hmatching : SelectedDiagonalMatchingFails configuration)
    (hred : redSiblingTriangleFailure configuration (.endpoint 0))
    (hblue : blueSiblingTriangleFailure configuration (.endpoint 0))
    (hweighted : weightedPairScore configuration.rootDisplacement barC lambda mu
      (configuration.redDisplacement .left) (configuration.redDisplacement .right)
      (configuration.bluePullback .left) (configuration.bluePullback .right) ≤ 0) :
    ∃ packing : SixPointPacking configuration, 0 ≤ packing.score barS := by
  rcases exists_nonnegative_score_or_rootEdge_type11_pair configuration h hmatching hred hblue with
    hpacking | htype11
  · exact hpacking
  · have hq₁ := firstActiveFailureSlack_nonneg h hmatching
    have hq₂ := secondActiveFailureSlack_pos h hred hblue
    have hq₃ := thirdActiveFailureSlack_pos h htype11.1 htype11.2
    have hpositive := activeFailureCombination_pos hlambda hmu hq₁ hq₂ hq₃
    rw [← weightedPairScore_configuration_eq_activeFailureCombination] at hpositive
    exact (not_lt_of_ge hweighted hpositive).elim

end LeanPool.Besicovitch
end
end
