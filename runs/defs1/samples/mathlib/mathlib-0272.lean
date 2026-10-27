@[expose] public section

open Opposite CategoryTheory Limits

noncomputable section

universe u v₁ v₂ v₃ u₁ u₂ u₃

namespace localCohomology

section LocalCohomologyEquiv

variable {R : Type u} [CommRing R]

variable {J K : Ideal R}

/-- The natural isomorphism between local cohomology defined using the `of_self_le_radical`
diagram, assuming `J.radical = K.radical`. -/
def SelfLERadical.isoOfSameRadical (hJK : J.radical = K.radical) (i : ℕ) :
    ofSelfLERadical J i ≅ ofSelfLERadical K i :=
  (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm

end LocalCohomologyEquiv
end localCohomology
end
end
