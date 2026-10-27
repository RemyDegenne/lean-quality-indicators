@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

namespace ArbitraryRowSameAxisDiamondResidualSuffixPartition

open MetricCodes.Spherical.HigherChannel

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute

/-- The axial lowering-path prefix with the pivot inserted, followed by its connecting
polarization. -/
def insertedDiamondPrefix {r n : ℕ}
    (target pivot : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1))) (next : Fin (r + 1)) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  (axialCoordinateLowerPath
    (polarizationPathStart target (insert pivot S)) k (front ++ [pivot])).comp
      (polarization r n next pivot)

end ArbitraryRowSameAxisDiamondResidualSuffixPartition
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
