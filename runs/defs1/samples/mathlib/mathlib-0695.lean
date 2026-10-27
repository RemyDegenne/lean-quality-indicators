@[expose] public section

open CategoryTheory CategoryTheory.Preadditive

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

attribute [instance] Mat_.fintype

namespace Mat_

variable {C}

namespace Hom

open scoped Classical in
/-- The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom congr(M.X $h) else 0

end Hom
end Mat_
end CategoryTheory
end
end
