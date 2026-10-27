@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankGTTransverseWignerEckartPhase

open MetricCodes.Spherical.HigherChannel

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalEdgeRaisingGram

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre

open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCasimirEmbedding

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity

open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

open MetricCodes.Spherical.HigherRepresentationGraph

open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

/-- The transverse positive-sector map normalized by its positive Gram scalar to a linear
isometry. -/
def normalizedGTTransversePositiveSector
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu nu : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hmunu : mu = raiseWeight nu row)
    (hmu : Interlaces lam mu)
    (hnu : Interlaces lam nu)
    (hnuGram : PositiveGelfandTsetlinFischerGram
      (n := n) lam nu hnu) :
    HarmonicYoungSpace (n := n) mu →ₗᵢ[ℝ]
      (SpherePacking.Euclidean (n + 1) ⊗[ℝ]
        HarmonicYoungSpace (n := n + 1) lam) :=
  SpherePacking.HarmonicCoordinateOperators.normalizedChannelIsometry
    (gtTransversePositiveSector lam mu nu row hmunu hnu hnuGram)
    (internalRowLowerGramScalar mu row)
    (by
      subst mu
      exact gtTransversePositiveSector_gram_pos nu row
        (interlaces_antitone_stabilizer hnu))
    (gtTransversePositiveSector_inner lam mu nu row
      hmunu hmu hnu hnuGram)

end AllRankGTTransverseWignerEckartPhase
end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
