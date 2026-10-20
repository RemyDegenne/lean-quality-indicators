@[expose] public section

open CategoryTheory

universe uR uS uT vR vS vT w

namespace KTheory

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

namespace ProjectiveClass

variable (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)

theorem equivOfModuleEquivalence_refl :
    equivOfModuleEquivalence
        (CategoryTheory.Equivalence.refl (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) =
      AddEquiv.refl (ProjectiveClass R) := by
  apply AddEquiv.ext
  intro a
  refine ProjectiveClass.induction_on R a ?_
  intro X
  change classMap (CategoryTheory.Equivalence.refl
    (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) (ProjectiveClass.of R X) = ProjectiveClass.of R X
  exact (classMap_of_reference (CategoryTheory.Equivalence.refl
    (C := ModuleCat.{max uR vR} Rᵐᵒᵖ)) X).trans (ProjectiveClass.of_ulift R X)

end ProjectiveClass
end KTheory
end
