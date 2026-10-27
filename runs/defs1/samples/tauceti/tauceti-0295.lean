public section

namespace TauCeti

open _root_.TauCeti.QuadraticMap

open _root_.QuadraticMap (polar)

variable (R : Type*) [CommRing R] [Invertible (2 : R)]

variable {R}

variable (R) in
/-- The diagonal torus identifies the units with the special orthogonal group of the hyperbolic
plane. -/
noncomputable def hyperbolicTorusEquiv : Rˣ ≃* specialOrthogonalGroup (hyperbolicPlane R) :=
  MulEquiv.ofBijective (hyperbolicTorus R) ⟨hyperbolicTorus_injective, hyperbolicTorus_surjective⟩

end TauCeti
end
