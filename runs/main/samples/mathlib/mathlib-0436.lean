@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C D : Type*} [Category* C] [Category* D] (W₁ W₂ : MorphismProperty C)

namespace FunctorialFactorizationData

variable {W₁ W₂}

variable (data : FunctorialFactorizationData W₁ W₂)

section

variable {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'} (φ : Arrow.mk f ⟶ Arrow.mk g)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
lemma i_mapZ :
    (data.factorizationData f).i ≫ data.mapZ φ = φ.left ≫ (data.factorizationData g).i :=
  (data.i.naturality φ).symm

end
end FunctorialFactorizationData
end MorphismProperty
end CategoryTheory
end
