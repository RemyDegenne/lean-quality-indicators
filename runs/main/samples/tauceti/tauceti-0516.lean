public section

open CategoryTheory MonoidalCategory MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

namespace GradedQuasicoherentAlgebra

variable {X}

@[simp]
theorem degree_map_hom {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) (n : ℕ) :
    ((degree (X := X) n).map f).hom =
      eqToHom (degree_obj_obj A n) ≫ f.hom.hom.hom n ≫ eqToHom (degree_obj_obj B n).symm := by
  cases degree_obj_obj A n
  cases degree_obj_obj B n
  -- As for `toGradedModules_map`, eliminate the object equations before the identity laws.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end GradedQuasicoherentAlgebra
end
end AlgebraicGeometry
end TauCeti
end
