@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory CategoryTheory.Functor

namespace Cat

open Lean.PrettyPrinter.Delaborator in
/-- This prints `CategoryTheory.Cat.of X` as `↧X`. -/
@[app_delab CategoryTheory.Cat.of]
meta def delabOf : Delab := CategoryTheory.delabOf

end Cat
end CategoryTheory
end
