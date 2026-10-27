@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace K0

/-- The additive map on K₀ induced by right scalar extension along a unital
ring homomorphism. This is the group-completion extension of the induced
class map, giving the change-of-rings functoriality of Weibel's *The K-book*,
Chapter II. -/
@[no_expose]
noncomputable def map (φ : R →+* S) : K0 R →+ K0 S :=
  lift R ((ofClass S).comp (ProjectiveClass.map φ))

end K0
end KTheory
end
