@[expose] public section

noncomputable section

open scoped nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- Given a maximal ideal `v` and an ideal `I` of `R`, `maxPowDividing` returns the maximal
  power of `v` dividing `I`. -/
def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R :=
  v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

end
end
