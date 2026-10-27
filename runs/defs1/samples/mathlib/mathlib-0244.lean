@[expose] public section

universe v v₁ u₁ u w

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

namespace SheafOfModules

variable {R}

variable (R)

variable {R}

variable (R) in
/-- The functor which sends a sheaf of modules to its type of sections. -/
@[simps]
def sectionsFunctor : SheafOfModules.{v} R ⥤ Type _ where
  obj M := M.sections
  map f := ↾(sectionsMap f)

end SheafOfModules
end
