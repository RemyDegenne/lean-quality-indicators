@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

namespace HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity

open MetricCodes.Spherical.HigherChannel

open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature

open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

/-- The padded pieri lower row used in the spherical-code argument. -/
def PaddedPieriLowerRow {r : ℕ} (lam : Fin (r + 1) → ℕ) :=
  {i : Fin (r + 1) //
    0 < lam i ∧ Antitone (loweredInternalYoungWeight lam i)}

end HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
end
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
