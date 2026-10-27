@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace SpherePacking

section

open scoped BigOperators InnerProductSpace

namespace HarmonicCertificateAssembly

/-- An orthonormal coordinate identification of homogeneous harmonic polynomials with Euclidean
space. -/
def harmonicPolynomialEuclideanEquiv
    (n m : ℕ) (hn : 0 < n) :
    harmonicHomogeneousSubmodule n m ≃ₗᵢ[ℝ]
      Euclidean (Gegenbauer.harmonicDimension n m) :=
  ((stdOrthonormalBasis ℝ (harmonicHomogeneousSubmodule n m)).reindex
    (finCongr (finrank_harmonicHomogeneousSubmodule hn m))).repr

end HarmonicCertificateAssembly
end
end SpherePacking
end MetricCodesNoncomputable
end
