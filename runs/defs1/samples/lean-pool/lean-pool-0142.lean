@[expose] public section

namespace TauCeti

namespace DavisKahan1970

namespace Section9

/-- Exact finite-data package required from an analytic realization of the
Section 9 free-beam example.  The record is a theorem boundary, not an
assumption installed globally: any concrete model must construct a value of
this type. -/
structure FreeBeamFiniteDataCertificate (ε : ℝ) where
  epsilon_pos : 0 < ε
  epsilon_lt_hundred : ε < 100
  /-- The value used in the third-eigenvalue lower-bound certificate. -/
  thirdEigenvalue : ℝ
  third_eigenvalue_gt_five_hundred : 500 < thirdEigenvalue
  /-- The initial two-by-two residual Gram matrix. -/
  initialResidualGram : SymmetricTwoByTwo
  initial_residual_gram_eq : initialResidualGram = residualGram ε
  /-- The lower Ritz value of the finite beam calculation. -/
  ritzLow : ℝ
  /-- The upper Ritz value of the finite beam calculation. -/
  ritzHigh : ℝ
  ritz_low_eq : ritzLow = Section9.ritzLow ε
  ritz_high_eq : ritzHigh = Section9.ritzHigh ε
  /-- The residual Gram matrix after orthogonal recentering. -/
  recenteredResidualGram : SymmetricTwoByTwo
  recentered_residual_gram_eq : recenteredResidualGram = orthogonalResidualGram ε

end Section9
end DavisKahan1970
end TauCeti
end
