@[expose] public section

universe v u

namespace CategoryTheory

open Category Preadditive

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]

namespace Pretriangulated

attribute [local simp] Triangle.eqToHom_hom₁ Triangle.eqToHom_hom₂ Triangle.eqToHom_hom₃
  shiftFunctorAdd_zero_add_hom_app shiftFunctorAdd_add_zero_hom_app
  shiftFunctorAdd'_eq_shiftFunctorAdd shift_shiftFunctorCompIsoId_inv_app

namespace Triangle

@[simp]
lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (Triangle C) a b =
      Triangle.shiftFunctorAdd' C a b _ rfl :=
  ShiftMkCore.shiftFunctorAdd_eq _ _ _

end Triangle
end Pretriangulated
end CategoryTheory
end
