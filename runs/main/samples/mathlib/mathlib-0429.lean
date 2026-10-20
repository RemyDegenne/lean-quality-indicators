@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace TopCat

variable {X Y Z : TopCat.{u}}

namespace Homotopy

variable {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)

@[simp]
lemma h_symm : h F.symm = (X ◁ I.symm) ≫ F.h := rfl

end Homotopy
end TopCat
end
