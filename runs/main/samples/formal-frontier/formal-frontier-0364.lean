@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section FieldRingEquivalence

variable (K : Type u) [hK : Field K]

theorem finrankRingEquiv_ofClass (a : ProjectiveClass K) :
    finrankRingEquiv K (ofClass K a) = (ProjectiveClass.finrankEquiv K a : ℤ) :=
  finrankEquiv_ofClass K a

end FieldRingEquivalence
end KTheory.K0
end
