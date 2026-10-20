public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

section Coordinates

variable {K : Type*} [Field K]

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

namespace TauCeti.GlobalNumberFields

/-- Assemble an idele from local units that are integral units at almost every finite place. -/
def ideleOfUnits (zi : ∀ w : InfinitePlace K, w.Completionˣ)
    (z : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (hz : ∀ᶠ v in Filter.cofinite, z v ∈ (v.adicCompletionIntegers K).units) :
    IdeleGroup R K :=
  MulEquiv.prodUnits.symm (MulEquiv.piUnits.symm zi, RestrictedProduct.mkUnit z hz)

end TauCeti.GlobalNumberFields
end Coordinates
end
end
