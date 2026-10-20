@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace ProjectiveClass

/-- The additive map on finite-projective right-module classes induced by
scalar extension along a unital ring homomorphism. It descends scalar
extension using preservation of isomorphisms, zero and direct sum, as in
Weibel's *The K-book*, Chapter II. -/
@[no_expose]
noncomputable def map (φ : R →+* S) : ProjectiveClass R →+ ProjectiveClass S :=
  lift R (mapValue φ) (mapValue_iso φ) (mapValue_zero φ) (mapValue_prod φ)

end ProjectiveClass
end KTheory
end
