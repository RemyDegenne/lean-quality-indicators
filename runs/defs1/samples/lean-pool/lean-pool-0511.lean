@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace SpherePacking

section

open scoped BigOperators InnerProductSpace

namespace HarmonicCoordinateChannels

/-- The axis-weighted projection-matrix feature, preceded by a zero channel. -/
def rawLiftChannel {n k L : ℕ}
    (f : Euclidean n →
      CertificateFibre n k →ₗᵢ[ℝ] CertificateAmbient n k L)
    (x : Euclidean n) : ProjectionChannelSpace n k L :=
  WithLp.toLp 2
    (Fin.cases (0 : ProjectionMatrixSpace n k L)
      (fun a : Fin n => x a • projectionMatrixFeature f x))

end HarmonicCoordinateChannels
end
end SpherePacking
end MetricCodesNoncomputable
end
