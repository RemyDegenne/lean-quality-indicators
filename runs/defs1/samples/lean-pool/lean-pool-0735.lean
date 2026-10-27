@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

open scoped BigOperators InnerProductSpace

namespace HigherHarmonicYoung.AllRankWeylBranchingRecurrence

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension

open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum

open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference

open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient

open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation

open MetricCodes.Spherical.HigherWeylBinomialDeterminant

open MetricCodes.Spherical.HigherHierarchy

/-- An integer branching coordinate between `branchLower lam i` and `lam i`, inclusive. -/
abbrev OrthogonalBranchCoordinate {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i : Fin (r + 1)) :=
  {a : Fin (lam i + 1) // branchLower lam i ≤ a.val}

end HigherHarmonicYoung.AllRankWeylBranchingRecurrence
end
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
