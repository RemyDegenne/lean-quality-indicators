namespace P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat

set_option autoImplicit false

namespace M4aP1R

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

open scoped nonZeroDivisors

namespace ClassFieldAxiom

section Carrier

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

noncomputable def principalIdeles : Subgroup (IdeleGroup R K) :=
  (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K)).range

end Carrier
end ClassFieldAxiom
end M4aP1R
end P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat
