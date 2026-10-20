public section

noncomputable section

open scoped NNReal

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [Algebra K A]
  [ContinuousSMul K A]

section TopologicallyFiniteType

attribute [local instance] Ideal.Quotient.field MaximalSpectrum.isMaximal

variable (K) (hA : IsTopologicallyFiniteType (algebraMap K A))

/-- **The classical points of an affinoid `K`-algebra** (Wedhorn, Example 7.58). For `A`
topologically of finite type over `K`, every maximal ideal `𝔪` is closed and has residue field
finite over `K` (Wedhorn, Proposition 5.61), so it has a classical point
`TauCeti.ValuationSpectrum.maximalIdealPoint` in `Spa (A, A°)`. -/
def maximalSpectrumToSpa (𝔪 : MaximalSpectrum A) : spa (powerBoundedSubring A) :=
  haveI := hA.finite_quotient_of_isMaximal 𝔪.asIdeal
  maximalIdealPoint K 𝔪.asIdeal (hA.isClosed_ideal 𝔪.asIdeal)

end TopologicallyFiniteType
end TauCeti.ValuationSpectrum
end
end
