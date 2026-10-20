@[expose] public section

open CategoryTheory

universe uR uS uT vR vS vT w

namespace KTheory

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

namespace ProjectiveClass

variable (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)

theorem equivOfModuleEquivalence_congr
    (e' : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)
    (α : e.functor ≅ e'.functor) :
    equivOfModuleEquivalence e = equivOfModuleEquivalence e' := by
  apply AddEquiv.ext
  intro a
  refine ProjectiveClass.induction_on R a ?_
  intro X
  let X' : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ :=
    ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)
  change classMap e (ProjectiveClass.of R X) = classMap e' (ProjectiveClass.of R X)
  calc
    classMap e (ProjectiveClass.of R X) =
        ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X') :=
      classMap_of_reference e X
    _ = ProjectiveClass.of S ((finiteProjectiveEquivalence e').functor.obj X') :=
      ProjectiveClass.of_eq_of_equiv S ((finiteProjectiveEquivalence e).functor.obj X')
        (N := (finiteProjectiveEquivalence e').functor.obj X') (α.app X'.obj).toLinearEquiv
    _ = classMap e' (ProjectiveClass.of R X) := (classMap_of_reference e' X).symm

end ProjectiveClass
end KTheory
end
