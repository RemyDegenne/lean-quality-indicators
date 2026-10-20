@[expose] public section

universe uR uS uM uN

open CategoryTheory

open scoped TensorProduct

namespace ModuleCat.RightExtension

section RingTarget

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S]

variable (φ : R →+* S)

@[simp]
theorem tensorProductObj_coe (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    (tensorProductObj φ M : Type (max uM uS)) =
      TensorProduct R
        ((ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj M)
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) := rfl

end RingTarget
end ModuleCat.RightExtension
end
