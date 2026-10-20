@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTWallSectorIsometry

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorGram

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression

open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)

open MetricCodes.Spherical.HigherYoungMixedGapAxisProbability

/-- The transverse wall-sector map normalized by its positive Gram scalar to a linear isometry. -/
def normalizedGTTransverseWallSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hn : 2 * (r + 1) + 5 ≤ n + 1)
    (hlast : 0 < lam (Fin.last (r + 1))) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransverseWallSector lam mu h hn hlast)
    (gtWallSectorGram n mu)
    (gtWallSectorGram_pos lam mu h hn hlast)
    (gtTransverseWallSector_inner lam mu h hn hlast)

end AllRankGTWallSectorIsometry
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
