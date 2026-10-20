@[expose] public section

open CategoryTheory

universe uR uS uT vR vS vT w

namespace KTheory

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

namespace ProjectiveClass

variable (e : ModuleCat.{max uR vR} Rᵐᵒᵖ ≌ ModuleCat.{max uS vS} Sᵐᵒᵖ)

theorem equivOfModuleEquivalence_trans {T : Type uT} [Ring T]
    (d : ModuleCat.{max uS vS} Sᵐᵒᵖ ≌ ModuleCat.{max uT vT} Tᵐᵒᵖ) :
    equivOfModuleEquivalence (e.trans d) =
      (equivOfModuleEquivalence e).trans (equivOfModuleEquivalence d) := by
  apply AddEquiv.ext
  intro a
  refine ProjectiveClass.induction_on R a ?_
  intro X
  let X' : ModuleCat.FiniteProjective.{uR, max uR vR} Rᵐᵒᵖ :=
    ModuleCat.FiniteProjective.of Rᵐᵒᵖ (ULift.{vR} X)
  change classMap (e.trans d) (ProjectiveClass.of R X) =
    classMap d (classMap e (ProjectiveClass.of R X))
  calc
    classMap (e.trans d) (ProjectiveClass.of R X) =
        ProjectiveClass.of T ((finiteProjectiveEquivalence (e.trans d)).functor.obj X') :=
      classMap_of_reference (e.trans d) X
    _ = classMap d
        (ProjectiveClass.of S ((finiteProjectiveEquivalence e).functor.obj X')) :=
      (classMap_of d ((finiteProjectiveEquivalence e).functor.obj X')).symm
    _ = classMap d (classMap e (ProjectiveClass.of R X)) :=
      congrArg (classMap d) (classMap_of_reference e X).symm

end ProjectiveClass
end KTheory
end
