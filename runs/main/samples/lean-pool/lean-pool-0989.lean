@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

theorem not_redEndpoint_zero_and_blueBalanced_one
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.endpoint 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 1)) := by
  rintro ⟨hred, hblue⟩
  have hpsep := SixPointConfiguration.two_mul_le_dist_redDisplacement h
  have hwsep := SixPointConfiguration.two_mul_le_dist_bluePullback h
  rw [barS, dist_eq_norm] at hpsep hwsep
  have hcertificate := tangentCertificate_e0s1 configuration.rootDisplacement
    (configuration.redDisplacement .left) (configuration.redDisplacement .right)
    (configuration.bluePullback .left) (configuration.bluePullback .right)
    (SixPointConfiguration.norm_rootDisplacement h)
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_redDisplacement_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp))
    (SixPointConfiguration.norm_bluePullback_le_one h (by simp)) (by linarith) (by linarith)
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redEndpointReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 1 hblue
  have hpositive : 0 < diagonalMatchingReducedSlack configuration +
      7 * redEndpointReducedSlack configuration 0 +
      13 * blueBalancedReducedSlack configuration 1 := by
    nlinarith
  simp only [diagonalMatchingReducedSlack, redEndpointReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm] at hpositive
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild] at hpositive
  nlinarith

end LeanPool.Besicovitch
end
end
