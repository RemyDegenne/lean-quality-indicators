public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The inclusion of the integer units into the elements that are units at the finite part.  Its
composition with the residue-and-sign presentation is the unit obstruction in the ray class exact
sequence. -/
noncomputable def unitsToPrimeToSubgroup (𝔪 : Modulus K) :
    (𝓞 K)ˣ →* primeToSubgroup 𝔪 :=
  MonoidHom.codRestrict (Units.map (algebraMap (𝓞 K) K).toMonoidHom) _
    (unitsMap_mem_primeToSubgroup 𝔪)

end TauCeti.GlobalNumberFields
end
