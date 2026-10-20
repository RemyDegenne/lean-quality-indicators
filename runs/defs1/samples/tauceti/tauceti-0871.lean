public section

open WithConv

namespace TauCeti

universe u v w

namespace DiagonalizableGroup

variable {R : Type u} {A : Type v} {G : Type w}

variable [CommSemiring R] [CommSemiring A] [Algebra R A] [CommGroup G]

/-- Algebra maps out of `R[G]` are the same as characters `G →* Aˣ` of `G`. -/
@[expose] noncomputable def pointEquiv : (MonoidAlgebra R G →ₐ[R] A) ≃ (G →* Aˣ) :=
  (MonoidAlgebra.lift R A G).symm.trans MonoidHom.toHomUnitsMulEquiv.toEquiv

end DiagonalizableGroup
end TauCeti
end
