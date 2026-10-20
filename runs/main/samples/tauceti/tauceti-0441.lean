public section

namespace IsDedekindDomain.FiniteAdeleRing

open HeightOneSpectrum Topology

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem unitsProj_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (unitsProj K v) :=
  (leftInverse_unitsProj_unitsOfAdicCompletion v).surjective

end IsDedekindDomain.FiniteAdeleRing
end
