open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct

open scoped Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section Adelic

variable (N : Ideal R)

def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) := (finiteLevelOne R K N).comap (glFin R K)

end Adelic
end NumberField.AdelicLevel
end
