@[expose] public section

namespace CategoryTheory

universe v v₂ u₁ u₂

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]

variable (F : C → D)

variable {D}

namespace InducedCategory

variable {F}

/-- Construct a morphism in the induced category
from a morphism in the original category. -/
@[simps] def homMk {X Y : InducedCategory D F} (f : F X ⟶ F Y) : X ⟶ Y where
  hom := f

end InducedCategory
end Induced
end CategoryTheory
end
