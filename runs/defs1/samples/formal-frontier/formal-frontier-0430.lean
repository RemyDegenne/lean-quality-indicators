@[expose] public section

universe uR uS uT uM uN

open CategoryTheory

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

section SemilinearHomEquiv

universe uX

variable {X : Type uX} [AddCommGroup X] [Module Sᵐᵒᵖ X]

/-- The canonical semilinear map from a right module to its extension of
scalars, sending `m` to `m ⊗ 1`. -/
def tmulOne : M →ₛₗ[RingHom.op f] Obj f M :=
  toSemilinear f LinearMap.id

end SemilinearHomEquiv
end ModuleCat.RightExtension
end
