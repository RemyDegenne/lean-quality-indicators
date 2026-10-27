@[expose] public section

noncomputable section

open CategoryTheory

universe w v u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{v})

/-- `sheafOfModulesEquivOver` takes `R.over U` to `R |_ U`. -/
def sheafOfModulesEquivOverUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ := .refl _

end TopologicalSpace.Opens
end
end
