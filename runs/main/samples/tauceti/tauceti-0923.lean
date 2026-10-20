public section

universe v u v' u'

namespace TauCeti.MorphismIdeal

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

section Ring

variable (R : Type*) [Ring R] [Linear R C] (I : MorphismIdeal C)

@[simp]
theorem homLinearEquiv_mk {X Y : C} (f : X ⟶ Y) :
    I.homLinearEquiv R X Y (Submodule.Quotient.mk f) = I.quotientFunctor.map f := by
  rw [homLinearEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ f

end Ring
end TauCeti.MorphismIdeal
end
