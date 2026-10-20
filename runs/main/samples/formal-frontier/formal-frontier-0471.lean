@[expose] public section

open CategoryTheory

universe uR uS uT vR vS vT w

namespace KTheory

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

namespace ProjectiveClass

variable (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)

theorem equivOfModuleEquivalence_symm :
    (equivOfModuleEquivalence e).symm =
      equivOfModuleEquivalence (R := S) (S := R) e.symm := by
  apply AddEquiv.ext
  intro b
  rfl

end ProjectiveClass
end KTheory
end
